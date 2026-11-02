import EinsteinFull.Regeneration.SplitSegmentSequence
import EinsteinRelation.Environment.FieldMeasurability

/-!
# Compatibility of the canonical infinite split segments

The joint prefix/next-segment law retains the transition correlations. It
implies that the environment stays equal to the input at every index. If the
actual path law starts at its stated position, all adjacent endpoints agree
on one event of full measure. These facts prepare continuous-path gluing; they
do not identify a martingale law or prove locality.
-/

open MeasureTheory ProbabilityTheory Preorder
open scoped NNReal ENNReal

noncomputable section
namespace EinsteinFull.Regeneration
open EinsteinRelation EinsteinRelation.Regeneration

private theorem map_traj_next {S : Type*} [MeasurableSpace S]
    (κ : (n : ℕ) → Kernel ((j : Finset.Iic n) → S) S)
    [∀ n, IsMarkovKernel (κ n)] (n : ℕ) :
    (Kernel.traj (X := fun _ : ℕ => S) κ n).map (fun s => s (n + 1)) = κ n := by
  have heval : (fun s : ℕ → S => s (n + 1)) =
      (fun s : (j : Finset.Iic (n + 1)) → S =>
        s ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩) ∘ frestrictLe (n + 1) := rfl
  rw [heval, Kernel.map_comp_right _ (measurable_frestrictLe _) (measurable_pi_apply _),
    Kernel.traj_map_frestrictLe, Kernel.partialTraj_succ_self,
    ← Kernel.map_comp_right _ (measurable_IicProdIoc (X := fun _ : ℕ => S))
      (measurable_pi_apply (⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic (n + 1)))]
  have hlast :
      (fun s : (j : Finset.Iic (n + 1)) → S =>
        s ⟨n + 1, Finset.mem_Iic.mpr le_rfl⟩) ∘ IicProdIoc (X := fun _ : ℕ => S) n (n + 1) =
      (fun s : (j : Finset.Ioc n (n + 1)) → S =>
        s ⟨n + 1, Finset.mem_Ioc.mpr ⟨Nat.lt_succ_self n, le_rfl⟩⟩) ∘ Prod.snd := by
    funext s
    simp only [Function.comp_apply, IicProdIoc_def, Nat.not_succ_le_self, ↓reduceDIte]
  rw [hlast, Kernel.map_comp_right _ measurable_snd (measurable_pi_apply _),
    ← Kernel.snd_eq, Kernel.snd_prod, ← Kernel.map_comp_right]
  · exact Kernel.map_id _
  · exact (MeasurableEquiv.piSingleton (X := fun _ : ℕ => S) n).measurable
  · exact measurable_pi_apply _

variable {d : ℕ} (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d)
  (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (hR : 0 < R)
  (P : QuenchedPathLaws d) [IsMarkovKernel P]
  (hminor : ∀ ω : FieldPair d,
    EinsteinFull.External.Source.GMP.HasSourceMinorization
      (fun x => P (x, ω)) Δ δ R i)

include hδ₁

instance isMarkovKernel_splitSegmentExtensionKernel (n : ℕ) :
    IsMarkovKernel (splitSegmentExtensionKernel Δ δ R i hδ₀ hδ₁ hR P hminor n) := by
  unfold splitSegmentExtensionKernel
  infer_instance

/-- The prefix and its next actual segment have precisely the iterated joint law. -/
theorem splitSegmentSequenceKernel_prefix_next (n : ℕ) :
    (splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor).map
        (fun s => (frestrictLe n s, s (n + 1))) =
      (Kernel.id ×ₖ splitSegmentHistoryKernel Δ δ R i hδ₀ hR P hminor n) ∘ₖ
        (splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor).map (frestrictLe n) := by
  letI : ∀ k, IsMarkovKernel
      (splitSegmentHistoryKernel Δ δ R i hδ₀ hR P hminor k) :=
    fun k => isMarkovKernel_splitSegmentHistoryKernel Δ δ R i hδ₀ hδ₁ hR P hminor k
  have h := congrArg (fun κ => κ.map (fun p => (p.1, p.2 (n + 1))))
    (splitSegmentSequenceKernel_prefix_joint Δ δ R i hδ₀ hδ₁ hR P hminor n)
  change ((Kernel.id ×ₖ splitSegmentExtensionKernel Δ δ R i hδ₀ hδ₁ hR P hminor n) ∘ₖ
    (splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor).map (frestrictLe n)).map
      (Prod.map id (fun s => s (n + 1))) = _ at h
  rw [Kernel.map_comp, ← Kernel.map_prod_map _ _ measurable_id (measurable_pi_apply _),
    Kernel.map_id] at h
  rw [← Kernel.map_comp_right _ (by fun_prop) (by fun_prop)] at h
  rw [splitSegmentExtensionKernel, map_traj_next] at h
  exact h.symm

private theorem ae_sequence_pair
    (p : SplitSegmentState d → SplitSegmentState d → Prop)
    (hp : MeasurableSet {q : SplitSegmentState d × SplitSegmentState d | p q.1 q.2})
    (hstep : ∀ u, ∀ᵐ v ∂splitSegmentStepKernel Δ δ R i hδ₀ hR P hminor u, p u v)
    (a : Vec d × FieldPair d) (n : ℕ) :
    ∀ᵐ s ∂splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor a,
      p (s n) (s (n + 1)) := by
  letI := isMarkovKernel_splitSegmentHistoryKernel Δ δ R i hδ₀ hδ₁ hR P hminor n
  let last : Finset.Iic n := ⟨n, Finset.mem_Iic.mpr le_rfl⟩
  have hp' : MeasurableSet
      {q : ((j : Finset.Iic n) → SplitSegmentState d) × SplitSegmentState d |
        p (q.1 last) q.2} :=
    hp.preimage (show Measurable (fun q :
      ((j : Finset.Iic n) → SplitSegmentState d) × SplitSegmentState d =>
        (q.1 last, q.2)) from by fun_prop)
  have hprod (u : (j : Finset.Iic n) → SplitSegmentState d) :
      ∀ᵐ q ∂(Kernel.id ×ₖ splitSegmentHistoryKernel Δ δ R i hδ₀ hR P hminor n) u,
        p (q.1 last) q.2 := by
    rw [ae_iff]
    change ((Kernel.id ×ₖ splitSegmentHistoryKernel Δ δ R i hδ₀ hR P hminor n) u)
      {q | p (q.1 last) q.2}ᶜ = 0
    rw [Kernel.id_prod_apply' _ _ hp'.compl]
    exact (ae_iff).mp (hstep (u last))
  have hcomp := Kernel.ae_comp_of_ae_ae hp' (ae_of_all
    ((splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor).map (frestrictLe n) a) hprod)
  rw [← splitSegmentSequenceKernel_prefix_next,
    Kernel.map_apply _ (by fun_prop)] at hcomp
  exact ae_of_ae_map (by fun_prop) hcomp

/-- Forgetting the environment and coin in the initial state recovers the
actual original path kernel. -/
theorem map_splitInitialStateKernel_path :
    (splitInitialStateKernel Δ δ R i hδ₀ hR P hminor).map (fun u => u.2.1) = P := by
  letI := isMarkovKernel_oneIntervalSplitKernel Δ δ R i hδ₀ hδ₁ hR P hminor
  change (splitInitialStateKernel Δ δ R i hδ₀ hR P hminor).map
    (Prod.fst ∘ Prod.snd) = P
  rw [Kernel.map_comp_right _ measurable_snd measurable_fst,
    splitInitialStateKernel, ← Kernel.snd_eq, Kernel.snd_prod]
  ext a : 1
  rw [Kernel.map_apply _ measurable_fst]
  exact map_oneIntervalSplitKernel_fst Δ δ R i hδ₀ hδ₁ hR P hminor a

/-- All segment environments equal the actual input environment simultaneously. -/
theorem ae_splitSegmentSequenceKernel_environment (a : Vec d × FieldPair d) :
    ∀ᵐ s ∂splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor a,
      ∀ n, (s n).1 = a.2 := by
  letI : PolishSpace (CoefficientField d) := Localization.coefficientField_polish d
  letI : PolishSpace (FieldPair d) := inferInstance
  have hzero : ∀ᵐ s ∂splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor a,
      (s 0).1 = a.2 := by
    have hinit : ∀ᵐ u ∂splitInitialStateKernel Δ δ R i hδ₀ hR P hminor a,
        u.1 = a.2 := by
      have he : (splitInitialStateKernel Δ δ R i hδ₀ hR P hminor a).map Prod.fst =
          Measure.dirac a.2 := by
        rw [← Kernel.map_apply _ measurable_fst,
          map_splitInitialStateKernel_environment (hδ₁ := hδ₁), Kernel.deterministic_apply]
      apply ae_of_ae_map (p := fun ω : FieldPair d => ω = a.2) measurable_fst.aemeasurable
      rw [he]
      exact (ae_dirac_iff (measurableSet_singleton _)).mpr rfl
    apply ae_of_ae_map (p := fun u : SplitSegmentState d => u.1 = a.2)
      (show Measurable (fun s : ℕ → SplitSegmentState d => s 0) from
        measurable_pi_apply 0).aemeasurable
    rwa [← Kernel.map_apply _ (measurable_pi_apply (0 : ℕ)),
      map_splitSegmentSequenceKernel_zero]
  have hsucc (n : ℕ) :
      ∀ᵐ s ∂splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor a,
        (s (n + 1)).1 = (s n).1 := by
    apply ae_sequence_pair Δ δ R i hδ₀ hδ₁ hR P hminor
      (fun u v => v.1 = u.1) (measurableSet_eq_fun (by fun_prop) (by fun_prop)) _ a n
    intro u
    apply ae_of_ae_map (p := fun ω : FieldPair d => ω = u.1) measurable_fst.aemeasurable
    rw [← Kernel.map_apply _ measurable_fst,
      map_splitSegmentStepKernel_environment (hδ₁ := hδ₁), Kernel.deterministic_apply]
    exact (ae_dirac_iff (measurableSet_singleton _)).mpr rfl
  filter_upwards [hzero, ae_all_iff.mpr hsucc] with s hs₀ hs
  intro n
  induction n with
  | zero => exact hs₀
  | succ n hn => exact (hs n).trans hn

/-- If the actual path law starts at its input position, adjacent sampled
segments have matching endpoints, simultaneously for every index. -/
theorem ae_splitSegmentSequenceKernel_endpoints
    (hstart : ∀ a, ∀ᵐ γ ∂P a, γ 0 = a.1) (a : Vec d × FieldPair d) :
    ∀ᵐ s ∂splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor a,
      (s 0).2.1 0 = a.1 ∧ ∀ n, (s (n + 1)).2.1 0 = (s n).2.1 Δ := by
  have hinit (b : Vec d × FieldPair d) :
      ∀ᵐ u ∂splitInitialStateKernel Δ δ R i hδ₀ hR P hminor b, u.2.1 0 = b.1 := by
    apply ae_of_ae_map (p := fun γ : Path d => γ 0 = b.1)
      (by fun_prop : Measurable (fun u : SplitSegmentState d => u.2.1)).aemeasurable
    rw [← Kernel.map_apply _ (by fun_prop), map_splitInitialStateKernel_path (hδ₁ := hδ₁)]
    exact hstart b
  have hzero : ∀ᵐ s ∂splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor a,
      (s 0).2.1 0 = a.1 := by
    apply ae_of_ae_map (p := fun u : SplitSegmentState d => u.2.1 0 = a.1)
      (show Measurable (fun s : ℕ → SplitSegmentState d => s 0) from
        measurable_pi_apply 0).aemeasurable
    rw [← Kernel.map_apply _ (measurable_pi_apply (0 : ℕ)),
      map_splitSegmentSequenceKernel_zero]
    exact hinit a
  have hsucc (n : ℕ) :
      ∀ᵐ s ∂splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor a,
        (s (n + 1)).2.1 0 = (s n).2.1 Δ := by
    apply ae_sequence_pair Δ δ R i hδ₀ hδ₁ hR P hminor
      (fun u v => v.2.1 0 = u.2.1 Δ)
      (measurableSet_eq_fun (by fun_prop) (by fun_prop)) _ a n
    intro u
    exact hinit (u.2.1 Δ, u.1)
  exact hzero.and (ae_all_iff.mpr hsucc)

end EinsteinFull.Regeneration
