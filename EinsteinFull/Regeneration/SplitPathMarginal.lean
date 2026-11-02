import EinsteinFull.Regeneration.SplitFreshBits
import EinsteinFull.Regeneration.PathPrefixReconstruction

/-!
# Path marginal of the actual continuous split kernel

The canonical segment law is compared with the original path law through
complete grid prefixes. The original process's endpoint-conditioned Markov
restart law is a separate, explicit input; source minorization alone does not
imply it. The comparison retains the joint law of the prefix and next segment.
-/

open MeasureTheory ProbabilityTheory Preorder
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinFull.Regeneration
open EinsteinRelation EinsteinRelation.Regeneration

private theorem map_pair_of_prefix_transition {S U A B : Type*}
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

/-- A complete closed grid prefix read from a finite sampled-segment prefix. -/
def splitPathPrefix {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (n : ℕ)
    (u : (j : Finset.Iic n) → SplitSegmentState d) : Path d :=
  gmpPrefixPath ((n + 1 : ℕ) * Δ)
    (gluedSplitSegmentSample Δ hΔ (extendSplitSegmentPrefix n u)).1

/-- Reading the complete grid prefix from actual finite segments is measurable. -/
theorem measurable_splitPathPrefix {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (n : ℕ) :
    Measurable (splitPathPrefix (d := d) Δ hΔ n) :=
  (measurable_gmpPrefixPath _).comp
    (((measurable_gluedSplitSegmentSample Δ hΔ).comp
      (measurable_extendSplitSegmentPrefix n)).fst)

/-- The finite-prefix reading is exactly the prefix of the actual glued path. -/
theorem splitPathPrefix_restrict {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (n : ℕ) (s : ℕ → SplitSegmentState d) :
    splitPathPrefix Δ hΔ n (frestrictLe n s) =
      gmpPrefixPath ((n + 1 : ℕ) * Δ) (gluedSplitSegmentSample Δ hΔ s).1 := by
  exact (congrArg Prod.fst (stoppedHistory_gluedSplitSegmentSample_prefix Δ hΔ n s)).symm

/-- On compatible actual segments, adjoining the next interval recovers the
next complete grid prefix of the same glued path. -/
theorem extendPathPrefix_gluedSplitSegmentSample {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (s : ℕ → SplitSegmentState d)
    (hcompat : ∀ k, (s (k + 1)).2.1 0 = (s k).2.1 Δ) (n : ℕ) :
    extendPathPrefix ((n + 1 : ℕ) * Δ) Δ
        (gmpPrefixPath ((n + 1 : ℕ) * Δ) (gluedSplitSegmentSample Δ hΔ s).1,
          (s (n + 1)).2.1) =
      gmpPrefixPath ((n + 2 : ℕ) * Δ) (gluedSplitSegmentSample Δ hΔ s).1 := by
  let γ := (gluedSplitSegmentSample Δ hΔ s).1
  let a : ℝ≥0 := (n + 1 : ℕ) * Δ
  have hgrid : (n + 2 : ℕ) * Δ = a + Δ := by
    dsimp only [a]
    push_cast
    ring
  have hinterval (u : ℝ≥0) (hu : u ≤ Δ) :
      γ (a + u) = (s (n + 1)).2.1 u :=
    glueSplitSegments_interval Δ hΔ (fun k => (s k).2.1) hcompat (n + 1) u hu
  have hzero : γ a = (s (n + 1)).2.1 0 := by
    simpa only [add_zero] using hinterval 0 Δ.2
  apply ContinuousMap.ext
  intro t
  change γ (min (min t a) a) +
      ((s (n + 1)).2.1 (min Δ (t - a)) - (s (n + 1)).2.1 0) =
    γ (min t ((n + 2 : ℕ) * Δ))
  rw [min_assoc, min_self, hgrid]
  by_cases ht : t ≤ a
  · rw [min_eq_left ht, tsub_eq_zero_of_le ht, min_eq_right (zero_le (a := Δ)),
      sub_self, add_zero, min_eq_left (ht.trans (le_add_of_nonneg_right Δ.2))]
  · have hat : a ≤ t := le_of_not_ge ht
    rw [min_eq_right hat, hzero]
    have he : min t (a + Δ) = a + min Δ (t - a) := by
      rw [add_min, add_tsub_cancel_of_le hat, min_comm]
    rw [he, hinterval _ (min_le_left _ _)]
    abel

variable {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ R : ℝ) (i : Fin d)
  (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (hR : 0 < R)
  (P : QuenchedPathLaws d) [IsMarkovKernel P]
  (hminor : ∀ ω : FieldPair d,
    EinsteinFull.External.Source.GMP.HasSourceMinorization
      (fun x => P (x, ω)) Δ δ R i)

include hδ₁

/-- Forgetting the next coin retains exactly the original endpoint path kernel. -/
theorem map_splitSegmentHistoryKernel_path (n : ℕ) :
    (splitSegmentHistoryKernel Δ δ R i hδ₀ hR P hminor n).map (fun u => u.2.1) =
      P.comap (fun u : (j : Finset.Iic n) → SplitSegmentState d =>
        ((u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).2.1 Δ,
          (u ⟨n, Finset.mem_Iic.mpr le_rfl⟩).1)) (by fun_prop) := by
  rw [splitSegmentHistoryKernel, ← Kernel.comap_map_comm _ (by fun_prop) (by fun_prop),
    splitSegmentStepKernel, ← Kernel.comap_map_comm _ (by fun_prop) (by fun_prop),
    map_splitInitialStateKernel_path (hδ₁ := hδ₁)]
  rfl

/-- The actual prefix and next unsplit path have their joint transition law. -/
theorem splitSegmentSequenceKernel_prefix_next_path (n : ℕ) :
    (splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor).map
        (fun s => (frestrictLe n s, (s (n + 1)).2.1)) =
      (Kernel.id ×ₖ (splitSegmentHistoryKernel Δ δ R i hδ₀ hR P hminor n).map
        (fun u => u.2.1)) ∘ₖ
      (splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor).map (frestrictLe n) := by
  letI := isMarkovKernel_splitSegmentHistoryKernel Δ δ R i hδ₀ hδ₁ hR P hminor n
  have h := congrArg (fun κ => κ.map (Prod.map id (fun u : SplitSegmentState d => u.2.1)))
    (splitSegmentSequenceKernel_prefix_next Δ δ R i hδ₀ hδ₁ hR P hminor n)

  rw [← Kernel.map_comp_right _ (by fun_prop) (by fun_prop), Kernel.map_comp,
    ← Kernel.map_prod_map _ _ measurable_id (by fun_prop), Kernel.map_id] at h
  exact h

/-- The glued closed prefix and next actual sampled path have precisely the
endpoint-conditioned joint law; the fixed input environment is retained. -/
theorem splitSegmentSequenceKernel_glued_prefix_next_path
    (hstart : ∀ a, ∀ᵐ γ ∂P a, γ 0 = a.1) (a : Vec d × FieldPair d) (n : ℕ) :
    (splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor a).map
        (fun s => (gmpPrefixPath ((n + 1 : ℕ) * Δ)
          (gluedSplitSegmentSample Δ hΔ s).1, (s (n + 1)).2.1)) =
      ((splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor a).map
        (fun s => gmpPrefixPath ((n + 1 : ℕ) * Δ)
          (gluedSplitSegmentSample Δ hΔ s).1)).compProd
        (pathPrefixContinuation (P.comap (fun x : Vec d => (x, a.2))
          (measurable_id.prodMk measurable_const)) ((n + 1 : ℕ) * Δ)) := by
  let μ := splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor a
  let κ := (splitSegmentHistoryKernel Δ δ R i hδ₀ hR P hminor n).map
    (fun u => u.2.1)
  let L := pathPrefixContinuation (P.comap (fun x : Vec d => (x, a.2))
    (measurable_id.prodMk measurable_const)) ((n + 1 : ℕ) * Δ)
  letI := isMarkovKernel_splitSegmentHistoryKernel Δ δ R i hδ₀ hδ₁ hR P hminor n
  letI : IsMarkovKernel κ := Kernel.IsMarkovKernel.map _ (by fun_prop)
  have h := congrArg (fun K => K a)
    (splitSegmentSequenceKernel_prefix_next_path Δ δ R i hδ₀ hδ₁ hR P hminor n)

  rw [Kernel.map_apply _ (by fun_prop), Kernel.comp_apply,
    Kernel.map_apply _ (measurable_frestrictLe n)] at h
  have hjoint : μ.map (fun s => (frestrictLe n s, (s (n + 1)).2.1)) =
      (μ.map (frestrictLe n)).compProd κ := by
    rw [Measure.compProd_eq_comp_prod]
    exact h
  have hκ : ∀ᵐ s ∂μ, κ (frestrictLe n s) =
      L (splitPathPrefix Δ hΔ n (frestrictLe n s)) := by
    filter_upwards [ae_splitSegmentSequenceKernel_environment Δ δ R i hδ₀ hδ₁ hR P hminor a,
      ae_gluedSplitSegmentSample_interval Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart a]
      with s henv hinterval
    dsimp only [κ, L]
    rw [map_splitSegmentHistoryKernel_path (hδ₁ := hδ₁), Kernel.comap_apply,
      pathPrefixContinuation, Kernel.comap_apply, Kernel.comap_apply]
    change P ((s n).2.1 Δ, (s n).1) =
      P ((splitPathPrefix Δ hΔ n (frestrictLe n s)) ((n + 1 : ℕ) * Δ), a.2)
    rw [henv n, splitPathPrefix_restrict]
    congr 2
    change (s n).2.1 Δ = (gluedSplitSegmentSample Δ hΔ s).1
      (min ((n + 1 : ℕ) * Δ) ((n + 1 : ℕ) * Δ))
    rw [min_self]
    have he : (n + 1 : ℕ) * Δ = n * Δ + Δ := by push_cast; ring
    rw [he]
    exact (hinterval n Δ le_rfl).symm
  have hresult := map_pair_of_prefix_transition μ (frestrictLe n)
    (splitPathPrefix Δ hΔ n) (fun s => (s (n + 1)).2.1)
    (measurable_frestrictLe n) (measurable_splitPathPrefix Δ hΔ n)
    (by fun_prop) κ L hjoint hκ
  simpa only [splitPathPrefix_restrict] using hresult

/-- If the original path law has its actual joint Markov restart law, the
canonical glued segment sequence has exactly that whole continuous-path law.
The restart premise is about the original process, not the constructed one. -/
theorem map_splitSegmentSequenceKernel_glued_path
    (hstart : ∀ a, ∀ᵐ γ ∂P a, γ 0 = a.1) (a : Vec d × FieldPair d)
    (hrestart : ∀ n : ℕ,
      (P a).map (fun γ => (gmpPrefixPath ((n + 1 : ℕ) * Δ) γ,
        gmpShiftPath ((n + 1 : ℕ) * Δ) γ)) =
      ((P a).map (gmpPrefixPath ((n + 1 : ℕ) * Δ))).compProd
        (pathPrefixContinuation (P.comap (fun x : Vec d => (x, a.2))
          (measurable_id.prodMk measurable_const)) ((n + 1 : ℕ) * Δ))) :
    (splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor a).map
      (fun s => (gluedSplitSegmentSample Δ hΔ s).1) = P a := by
  let μ := splitSegmentSequenceKernel Δ δ R i hδ₀ hδ₁ hR P hminor a
  let g := fun s : ℕ → SplitSegmentState d => (gluedSplitSegmentSample Δ hΔ s).1
  have hg : Measurable g := (measurable_gluedSplitSegmentSample Δ hΔ).fst
  have hfirst : μ.map (fun s => (s 0).2.1) = P a := by
    have h := congrArg (fun K => K a) (map_splitSegmentSequenceKernel_zero
      Δ δ R i hδ₀ hδ₁ hR P hminor)

    have hi := congrArg (fun K => K a)
      (map_splitInitialStateKernel_path Δ δ R i hδ₀ hδ₁ hR P hminor)

    rw [Kernel.map_apply _ (measurable_pi_apply 0)] at h
    rw [Kernel.map_apply _ (by fun_prop)] at hi
    change μ.map ((fun u : SplitSegmentState d => u.2.1) ∘
      (fun s : ℕ → SplitSegmentState d => s 0)) = P a
    rw [← Measure.map_map (show Measurable (fun u : SplitSegmentState d => u.2.1) from
      by fun_prop) (measurable_pi_apply (0 : ℕ))]
    exact (congrArg (Measure.map (fun u : SplitSegmentState d => u.2.1)) h).trans hi
  have hprefix (n : ℕ) :
      μ.map (fun s => gmpPrefixPath ((n + 1 : ℕ) * Δ) (g s)) =
        (P a).map (gmpPrefixPath ((n + 1 : ℕ) * Δ)) := by
    induction n with
    | zero =>
      simp only [zero_add, Nat.cast_one, one_mul]
      calc
        _ = μ.map (fun s => gmpPrefixPath Δ (s 0).2.1) := by
          apply Measure.map_congr
          filter_upwards [ae_gluedSplitSegmentSample_interval Δ hΔ δ R i hδ₀ hδ₁ hR P
            hminor hstart a] with s hs
          apply ContinuousMap.ext
          intro t
          simpa only [gmpPrefixPath, ContinuousMap.coe_mk, Nat.cast_zero, zero_mul, zero_add]
            using hs 0 (min t Δ) (min_le_right _ _)
        _ = (P a).map (gmpPrefixPath Δ) := by
          change μ.map (gmpPrefixPath Δ ∘ (fun s : ℕ → SplitSegmentState d => (s 0).2.1)) = _
          rw [← Measure.map_map (measurable_gmpPrefixPath _) (by fun_prop), hfirst]
    | succ n ih =>
      have hp : Measurable (fun s => (gmpPrefixPath ((n + 1 : ℕ) * Δ) (g s),
          (s (n + 1)).2.1)) :=
        ((measurable_gmpPrefixPath _).comp hg).prodMk (by fun_prop)
      have hgrid : ((n + 1 : ℕ) * Δ) + Δ = (n + 2 : ℕ) * Δ := by push_cast; ring
      calc
        _ = (μ.map (fun s => (gmpPrefixPath ((n + 1 : ℕ) * Δ) (g s),
            (s (n + 1)).2.1))).map (extendPathPrefix ((n + 1 : ℕ) * Δ) Δ) := by
          rw [Measure.map_map (measurable_extendPathPrefix _ _) hp]
          apply Measure.map_congr
          filter_upwards [ae_splitSegmentSequenceKernel_endpoints Δ δ R i hδ₀ hδ₁ hR P
            hminor hstart a] with s hs
          exact (extendPathPrefix_gluedSplitSegmentSample Δ hΔ s hs.2 n).symm
        _ = ((P a).map (fun γ => (gmpPrefixPath ((n + 1 : ℕ) * Δ) γ,
            gmpShiftPath ((n + 1 : ℕ) * Δ) γ))).map
              (extendPathPrefix ((n + 1 : ℕ) * Δ) Δ) := by
          rw [splitSegmentSequenceKernel_glued_prefix_next_path Δ hΔ δ R i hδ₀ hδ₁ hR P
            hminor hstart a n, ih, ← hrestart n]
        _ = (P a).map (gmpPrefixPath ((n + 2 : ℕ) * Δ)) := by
          rw [Measure.map_map (measurable_extendPathPrefix _ _)
            ((measurable_gmpPrefixPath _).prodMk (measurable_gmpShiftPath _))]
          congr 1
          funext γ
          exact (extendPathPrefix_prefix_shift _ Δ γ).trans
            (congrArg (fun t => gmpPrefixPath t γ) hgrid)
  apply pathMeasure_eq_of_grid_prefix Δ hΔ
  intro n
  rw [Measure.map_map (measurable_gmpPrefixPath _) hg]
  exact hprefix n

/-- The same constructed continuous-path/coin kernel has precisely the
original whole-path marginal, under the original process's Markov restart law. -/
theorem map_splitContinuousCouplingKernel_path
    (hstart : ∀ a, ∀ᵐ γ ∂P a, γ 0 = a.1) (a : Vec d × FieldPair d)
    (hrestart : ∀ n : ℕ,
      (P a).map (fun γ => (gmpPrefixPath ((n + 1 : ℕ) * Δ) γ,
        gmpShiftPath ((n + 1 : ℕ) * Δ) γ)) =
      ((P a).map (gmpPrefixPath ((n + 1 : ℕ) * Δ))).compProd
        (pathPrefixContinuation (P.comap (fun x : Vec d => (x, a.2))
          (measurable_id.prodMk measurable_const)) ((n + 1 : ℕ) * Δ))) :
    (splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor a).map Prod.fst = P a := by
  rw [splitContinuousCouplingKernel,
    Kernel.map_apply _ (measurable_gluedSplitSegmentSample Δ hΔ),
    Measure.map_map measurable_fst (measurable_gluedSplitSegmentSample Δ hΔ)]
  exact map_splitSegmentSequenceKernel_glued_path Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart a
    hrestart

end EinsteinFull.Regeneration
