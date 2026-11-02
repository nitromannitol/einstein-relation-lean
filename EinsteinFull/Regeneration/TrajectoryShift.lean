import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.Composition.Lemmas

/-!
# Deterministic time shifts of homogeneous kernel trajectories

These measure identities retain the complete sampled prefix and the entire
future sequence. They will be applied to the literal split-segment kernel;
no continuous-process restart or locality premise is used.
-/

open MeasureTheory ProbabilityTheory Preorder
noncomputable section
namespace EinsteinFull.Regeneration

/-- Shift an actual infinite sequence by a deterministic number of coordinates. -/
def sequenceShift {S : Type*} (n : ℕ) (s : ℕ → S) : ℕ → S := fun k => s (n + k)

theorem measurable_sequenceShift {S : Type*} [MeasurableSpace S] (n : ℕ) :
    Measurable (sequenceShift (S := S) n) :=
  Measurable.of_eval (fun k => measurable_pi_apply (n + k))

private def appendPrefix {S : Type*} (n : ℕ)
    (q : ((j : Finset.Iic n) → S) × S) : (j : Finset.Iic (n + 1)) → S :=
  fun j => if h : j.1 ≤ n then q.1 ⟨j, Finset.mem_Iic.mpr h⟩ else q.2

private theorem measurable_appendPrefix {S : Type*} [MeasurableSpace S] (n : ℕ) :
    Measurable (appendPrefix (S := S) n) := by
  apply Measurable.of_eval
  intro j
  by_cases h : j.1 ≤ n
  · simp only [appendPrefix, h, ↓reduceDIte]
    exact (measurable_pi_apply _).comp measurable_fst
  · simp only [appendPrefix, h, ↓reduceDIte]
    exact measurable_snd

private theorem appendPrefix_restrict {S : Type*} (n : ℕ) (s : ℕ → S) :
    appendPrefix n (frestrictLe n s, s (n + 1)) = frestrictLe (n + 1) s := by
  funext j
  dsimp only [appendPrefix]
  split_ifs with h
  · rfl
  · have hj : j.1 = n + 1 := by have := Finset.mem_Iic.mp j.2; omega
    exact congrArg s hj.symm

/-- Exact initial and joint prefix/next-coordinate laws determine the entire
sequence measure. The transition is allowed to depend on the full prefix. -/
theorem sequenceMeasure_eq_of_prefix_next {S : Type*} [MeasurableSpace S]
    (μ ν : Measure (ℕ → S)) [IsFiniteMeasure ν]
    (κ : (n : ℕ) → Kernel ((j : Finset.Iic n) → S) S)
    (hzero : μ.map (fun s => s 0) = ν.map (fun s => s 0))
    (hμ : ∀ n, μ.map (fun s => (frestrictLe n s, s (n + 1))) =
      (μ.map (frestrictLe n)).compProd (κ n))
    (hν : ∀ n, ν.map (fun s => (frestrictLe n s, s (n + 1))) =
      (ν.map (frestrictLe n)).compProd (κ n)) : μ = ν := by
  have hprefix (n : ℕ) : μ.map (frestrictLe n) = ν.map (frestrictLe n) := by
    induction n with
    | zero =>
      have he : (frestrictLe 0 : (ℕ → S) → _) =
          (fun x : S => fun _ : Finset.Iic 0 => x) ∘ (fun s => s 0) := by
        funext s j
        have hj : j.1 = 0 := Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp j.2)
        exact congrArg s hj
      rw [he, ← Measure.map_map (show Measurable (fun x : S => fun _ : Finset.Iic 0 => x) from
          Measurable.of_eval (fun _ => measurable_id))
        (measurable_pi_apply 0), ← Measure.map_map
        (show Measurable (fun x : S => fun _ : Finset.Iic 0 => x) from
          Measurable.of_eval (fun _ => measurable_id)) (measurable_pi_apply 0), hzero]
    | succ n ih =>
      have he : (frestrictLe (n + 1) : (ℕ → S) → _) =
          appendPrefix n ∘ (fun s => (frestrictLe n s, s (n + 1))) :=
        funext (fun s => (appendPrefix_restrict n s).symm)
      rw [he, ← Measure.map_map (measurable_appendPrefix n) (by fun_prop),
        ← Measure.map_map (measurable_appendPrefix n) (by fun_prop), hμ n, hν n, ih]
  apply IsProjectiveLimit.unique (P := fun I : Finset ℕ => ν.map I.restrict)
    (hν := fun _ => rfl)
  intro I
  change μ.map I.restrict = ν.map I.restrict
  have hm : Measurable (Finset.restrict₂ (π := fun _ : ℕ => S) I.subset_Iic_sup_id :
      ((j : Finset.Iic (I.sup id)) → S) → ((j : I) → S)) :=
    Finset.measurable_restrict₂ _
  calc
    μ.map I.restrict = (μ.map (frestrictLe (I.sup id))).map
        (Finset.restrict₂ (π := fun _ : ℕ => S) I.subset_Iic_sup_id) := by
      rw [Measure.map_map hm (measurable_frestrictLe _)]
      rfl
    _ = (ν.map (frestrictLe (I.sup id))).map
        (Finset.restrict₂ (π := fun _ : ℕ => S) I.subset_Iic_sup_id) := congrArg _ (hprefix _)
    _ = ν.map I.restrict := by
      rw [Measure.map_map hm (measurable_frestrictLe _)]
      rfl

private theorem map_trajectory_next {S : Type*} [MeasurableSpace S]
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

/-- An arbitrary kernel trajectory has its exact joint prefix/next law. -/
theorem trajectory_prefix_next_joint {S : Type*} [MeasurableSpace S]
    (κ : (n : ℕ) → Kernel ((j : Finset.Iic n) → S) S)
    [∀ n, IsMarkovKernel (κ n)] {a b : ℕ} (hab : a ≤ b)
    (u : (j : Finset.Iic a) → S) :
    (Kernel.traj (X := fun _ : ℕ => S) κ a u).map
        (fun s => (frestrictLe b s, s (b + 1))) =
      ((Kernel.traj (X := fun _ : ℕ => S) κ a u).map (frestrictLe b)).compProd
        (κ b) := by
  have h := congrArg (Measure.map (Prod.map id (fun s : ℕ → S => s (b + 1))))
    (Kernel.partialTraj_compProd_traj (κ := κ) hab u)
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at h
  rw [← Measure.compProd_map (measurable_pi_apply (b + 1))] at h
  rw [← Kernel.traj_map_frestrictLe_apply, map_trajectory_next] at h
  exact h.symm

/-- A homogeneous transition reads precisely the last actual sampled state. -/
def homogeneousHistoryKernel {S : Type*} [MeasurableSpace S] (κ : Kernel S S) (n : ℕ) :
    Kernel ((j : Finset.Iic n) → S) S :=
  κ.comap (fun u => u ⟨n, Finset.mem_Iic.mpr le_rfl⟩) (measurable_pi_apply _)

instance isMarkovKernel_homogeneousHistoryKernel {S : Type*} [MeasurableSpace S]
    (κ : Kernel S S) [IsMarkovKernel κ] (n : ℕ) :
    IsMarkovKernel (homogeneousHistoryKernel κ n) := by
  unfold homogeneousHistoryKernel
  infer_instance

/-- The actual infinite trajectory with a specified initial-state kernel. -/
def seededTrajectory {S A : Type*} [MeasurableSpace S] [MeasurableSpace A]
    (κ : Kernel S S) [IsMarkovKernel κ] (ι : Kernel A S) : Kernel A (ℕ → S) :=
  Kernel.traj (homogeneousHistoryKernel κ) 0 ∘ₖ
    ι.map (fun x => fun _ : Finset.Iic 0 => x)

instance isMarkovKernel_seededTrajectory {S A : Type*}
    [MeasurableSpace S] [MeasurableSpace A]
    (κ : Kernel S S) [IsMarkovKernel κ] (ι : Kernel A S) [IsMarkovKernel ι] :
    IsMarkovKernel (seededTrajectory κ ι) := by
  unfold seededTrajectory
  let _ := Kernel.IsMarkovKernel.map ι
    (show Measurable (fun x : S => fun _ : Finset.Iic 0 => x) from
      Measurable.of_eval (fun _ => measurable_id))
  infer_instance

/-- The seeded trajectory has exactly its prescribed initial-state kernel. -/
theorem map_seededTrajectory_zero {S A : Type*}
    [MeasurableSpace S] [MeasurableSpace A]
    (κ : Kernel S S) [IsMarkovKernel κ] (ι : Kernel A S) :
    (seededTrajectory κ ι).map (fun s => s 0) = ι := by
  have he : (fun s : ℕ → S => s 0) =
      (fun u : (j : Finset.Iic 0) → S => u ⟨0, Finset.mem_Iic.mpr le_rfl⟩) ∘
        frestrictLe 0 := rfl
  rw [seededTrajectory, Kernel.map_comp, he,
    Kernel.map_comp_right _ (measurable_frestrictLe 0) (measurable_pi_apply _),
    Kernel.traj_map_frestrictLe, Kernel.partialTraj_self,
    Kernel.id_map, Kernel.deterministic_comp_eq_map,
    ← Kernel.map_comp_right]
  · exact Kernel.map_id ι
  · exact Measurable.of_eval (fun _ => measurable_id)
  · exact measurable_pi_apply _
  · exact measurable_pi_apply _

/-- The entire sampled prefix and next coordinate retain the homogeneous transition. -/
theorem seededTrajectory_prefix_next_joint {S A : Type*}
    [MeasurableSpace S] [MeasurableSpace A]
    (κ : Kernel S S) [IsMarkovKernel κ] (ι : Kernel A S) [IsMarkovKernel ι]
    (a : A) (n : ℕ) :
    (seededTrajectory κ ι a).map (fun s => (frestrictLe n s, s (n + 1))) =
      ((seededTrajectory κ ι a).map (frestrictLe n)).compProd
        (homogeneousHistoryKernel κ n) := by
  have hjoint :
      (Kernel.traj (X := fun _ : ℕ => S) (homogeneousHistoryKernel κ) 0).map
          (fun s => (frestrictLe n s, s (n + 1))) =
        (Kernel.id ×ₖ homogeneousHistoryKernel κ n) ∘ₖ
          (Kernel.traj (X := fun _ : ℕ => S) (homogeneousHistoryKernel κ) 0).map (frestrictLe n) := by
    ext u : 1
    rw [Kernel.map_apply _ (by fun_prop), Kernel.comp_apply,
      Kernel.map_apply _ (measurable_frestrictLe n), ← Measure.compProd_eq_comp_prod]
    exact trajectory_prefix_next_joint _ (Nat.zero_le n) u
  rw [← Kernel.map_apply _ (by fun_prop), seededTrajectory, Kernel.map_comp, hjoint,
    Kernel.comp_assoc, ← Kernel.map_comp, Kernel.comp_apply,
    Kernel.map_apply _ (measurable_frestrictLe n), ← Measure.compProd_eq_comp_prod]

/-- Projecting an exact prefix transition retains its conditional law whenever
the transition depends on precisely the projected prefix. -/
theorem map_pair_of_prefix_transition {S U A B : Type*}
    [MeasurableSpace S] [MeasurableSpace U] [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure S) [IsFiniteMeasure μ] (p : S → U) (f : U → A) (v : S → B)
    (hp : Measurable p) (hf : Measurable f) (hv : Measurable v)
    (κ : Kernel U B) [IsFiniteKernel κ] (L : Kernel A B) [IsFiniteKernel L]
    (hjoint : μ.map (fun s => (p s, v s)) = (μ.map p).compProd κ)
    (hκ : ∀ᵐ s ∂μ, κ (p s) = L (f (p s))) :
    μ.map (fun s => (f (p s), v s)) = (μ.map (fun s => f (p s))).compProd L := by
  apply Measure.ext_prod
  intro E F hE hF
  have h := congrArg (fun ν : Measure (U × B) => ν ((f ⁻¹' E) ×ˢ F)) hjoint
  rw [Measure.map_apply (hp.prodMk hv) ((hE.preimage hf).prod hF),
    Measure.compProd_apply_prod (hE.preimage hf) hF,
    setLIntegral_map (hE.preimage hf) (κ.measurable_coe hF) hp] at h
  have hfp : Measurable (fun s => f (p s)) := hf.comp hp
  rw [Measure.map_apply (hfp.prodMk hv) (hE.prod hF),
    Measure.compProd_apply_prod hE hF,
    setLIntegral_map hE (L.measurable_coe hF) hfp]
  refine h.trans (lintegral_congr_ae ?_)
  filter_upwards [ae_restrict_of_ae hκ] with s hs
  exact congrArg (fun ν : Measure B => ν F) hs

private def shiftedPrefix {S : Type*} (a n : ℕ)
    (u : (j : Finset.Iic (a + 1 + n)) → S) : (j : Finset.Iic n) → S :=
  fun j => u ⟨a + 1 + j, Finset.mem_Iic.mpr (Nat.add_le_add_left (Finset.mem_Iic.mp j.2) _)⟩

private theorem measurable_shiftedPrefix {S : Type*} [MeasurableSpace S] (a n : ℕ) :
    Measurable (shiftedPrefix (S := S) a n) :=
  Measurable.of_eval (fun _ => measurable_pi_apply _)

/-- Discarding a deterministic prefix of a homogeneous trajectory gives the
whole trajectory sampled from the next transition at its actual last state. -/
theorem trajectory_shift {S : Type*} [MeasurableSpace S]
    (κ : Kernel S S) [IsMarkovKernel κ] (a : ℕ)
    (u : (j : Finset.Iic a) → S) :
    (Kernel.traj (X := fun _ : ℕ => S) (homogeneousHistoryKernel κ) a u).map
        (sequenceShift (a + 1)) =
      seededTrajectory κ κ (u ⟨a, Finset.mem_Iic.mpr le_rfl⟩) := by
  let μ := Kernel.traj (X := fun _ : ℕ => S) (homogeneousHistoryKernel κ) a u
  apply sequenceMeasure_eq_of_prefix_next _ _ (homogeneousHistoryKernel κ)
  · rw [Measure.map_map (measurable_pi_apply 0) (measurable_sequenceShift _)]
    change μ.map (fun s => s (a + 1)) = _
    rw [← Kernel.map_apply _ (measurable_pi_apply (a + 1)), map_trajectory_next,
      ← Kernel.map_apply _ (measurable_pi_apply 0), map_seededTrajectory_zero]
    rfl
  · intro n
    rw [Measure.map_map (by fun_prop) (measurable_sequenceShift _),
      Measure.map_map (measurable_frestrictLe n) (measurable_sequenceShift _)]
    have h := map_pair_of_prefix_transition μ (frestrictLe (a + 1 + n))
      (shiftedPrefix a n) (fun s => s (a + 1 + n + 1))
      (measurable_frestrictLe _) (measurable_shiftedPrefix _ _) (measurable_pi_apply _)
      (homogeneousHistoryKernel κ (a + 1 + n)) (homogeneousHistoryKernel κ n)
      (trajectory_prefix_next_joint _ (by omega) u) (Filter.Eventually.of_forall (fun _ => rfl))
    exact h
  · exact seededTrajectory_prefix_next_joint κ κ _

end EinsteinFull.Regeneration
