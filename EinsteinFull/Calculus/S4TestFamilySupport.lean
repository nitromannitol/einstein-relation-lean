import EinsteinFull.Calculus.S4GeneratorRegularitySupport
import Mathlib.Topology.Bases
import Mathlib.Topology.Metrizable.Basic

/-!
# A countable family of test functions that is dense with controlled derivatives

For every `f ∈ C_c^∞(ℝᵈ)` there is a sequence in a fixed countable subfamily `𝔉` of `C_c^∞`
such that `u_k`, `∂ⱼ u_k`, `∂ᵢ∂ⱼ u_k` are uniformly bounded and Lipschitz with a common constant
and converge pointwise (everywhere) to `f`, `∂ⱼ f`, `∂ᵢ∂ⱼ f`.  This is the countable reduction
of the test class used to see the martingale problem as a measurable relation.
-/

open Topology Filter
open scoped NNReal

namespace EinsteinFull
open EinsteinRelation

/-- The first coordinate derivative. -/
noncomputable def D1 {d : ℕ} (f : Vec d → ℝ) (j : Fin d) (y : Vec d) : ℝ :=
  fderiv ℝ f y (unitVector j)

/-- The second coordinate derivative `∂ᵢ ∂ⱼ f`. -/
noncomputable def D2 {d : ℕ} (f : Vec d → ℝ) (i j : Fin d) (y : Vec d) : ℝ :=
  fderiv ℝ (fun z => fderiv ℝ f z (unitVector j)) y (unitVector i)

/-- Bounded by `m` and `m`-Lipschitz. -/
def Reg {d : ℕ} (m : ℝ) (g : Vec d → ℝ) : Prop :=
  (∀ y, |g y| ≤ m) ∧ ∀ y z, |g y - g z| ≤ m * ‖y - z‖

theorem Reg.mono {d : ℕ} {m m' : ℝ} {g : Vec d → ℝ} (h : Reg m g) (hm : m ≤ m') : Reg m' g :=
  ⟨fun y => (h.1 y).trans hm,
    fun y z => (h.2 y z).trans (mul_le_mul_of_nonneg_right hm (norm_nonneg _))⟩

/-- Test functions whose first and second derivatives are `m`-regular. -/
def InH {d : ℕ} (m : ℝ) (f : Vec d → ℝ) : Prop :=
  (ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f) ∧ Reg m f ∧ (∀ j, Reg m (D1 f j)) ∧
    ∀ i j, Reg m (D2 f i j)

theorem exists_reg_of_contDiff {d : ℕ} {g : Vec d → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hc : HasCompactSupport g) : ∃ m : ℝ, Reg m g := by
  obtain ⟨C1, hC1⟩ := hg.continuous.bounded_above_of_compact_support hc
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hg (by simp)
  refine ⟨max C1 (K : ℝ), fun y => ?_, fun y z => ?_⟩
  · have := hC1 y
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  · have h := hK.dist_le_mul y z
    rw [Real.dist_eq, dist_eq_norm] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

theorem contDiff_D1 {d : ℕ} {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (j : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (D1 f j) :=
  ((contDiff_infty_iff_fderiv.1 hf).2).clm_apply contDiff_const

theorem hasCompactSupport_D1 {d : ℕ} {f : Vec d → ℝ} (hc : HasCompactSupport f) (j : Fin d) :
    HasCompactSupport (D1 f j) :=
  HasCompactSupport.fderiv_apply (𝕜 := ℝ) hc (unitVector j)

theorem D2_eq {d : ℕ} (f : Vec d → ℝ) (i j : Fin d) : D2 f i j = D1 (D1 f j) i := rfl

theorem exists_inH {d : ℕ} {f : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) : ∃ m : ℝ, InH m f := by
  obtain ⟨m0, h0⟩ := exists_reg_of_contDiff hf hc
  have h1 : ∀ j : Fin d, ∃ m : ℝ, Reg m (D1 f j) := fun j =>
    exists_reg_of_contDiff (contDiff_D1 hf j) (hasCompactSupport_D1 hc j)
  have h2 : ∀ i j : Fin d, ∃ m : ℝ, Reg m (D2 f i j) := fun i j => by
    rw [D2_eq]
    exact exists_reg_of_contDiff (contDiff_D1 (contDiff_D1 hf j) i)
      (hasCompactSupport_D1 (hasCompactSupport_D1 hc j) i)
  choose m1 hm1 using h1
  choose m2 hm2 using h2
  refine ⟨|m0| + ∑ j, |m1 j| + ∑ i, ∑ j, |m2 i j|, ⟨hf, hc⟩, ?_, fun j => ?_, fun i j => ?_⟩
  · refine h0.mono ?_
    have : 0 ≤ ∑ j, |m1 j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    have : 0 ≤ ∑ i, ∑ j, |m2 i j| :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith [le_abs_self m0]
  · refine (hm1 j).mono ?_
    have h := Finset.single_le_sum (f := fun j => |m1 j|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ j)
    have : 0 ≤ ∑ i, ∑ j, |m2 i j| :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith [le_abs_self (m1 j), abs_nonneg m0]
  · refine (hm2 i j).mono ?_
    have h := Finset.single_le_sum (f := fun j => |m2 i j|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ j)
    have h' := Finset.single_le_sum (f := fun i => ∑ j, |m2 i j|)
      (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have : 0 ≤ ∑ j, |m1 j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith [le_abs_self (m2 i j), abs_nonneg m0]

theorem tendsto_of_dense_lipschitz {d : ℕ} {m : ℝ} {g : ℕ → Vec d → ℝ} {g' : Vec d → ℝ}
    (hg : ∀ k, Reg m (g k)) (hg' : Reg m g') (q : ℕ → Vec d) (hq : DenseRange q)
    (hconv : ∀ n, Tendsto (fun k => g k (q n)) atTop (𝓝 (g' (q n)))) (y : Vec d) :
    Tendsto (fun k => g k y) atTop (𝓝 (g' y)) := by
  have hm : 0 ≤ m := (abs_nonneg _).trans (hg'.1 y)
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hδ : 0 < ε / (4 * (m + 1)) := by positivity
  obtain ⟨n, hn⟩ := hq.exists_dist_lt y hδ
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hconv n) (ε / 2) (by positivity)
  refine ⟨N, fun k hk => ?_⟩
  have h1 := (hg k).2 y (q n)
  have h2 := hg'.2 y (q n)
  have h3 := hN k hk
  rw [Real.dist_eq] at h3 ⊢
  rw [dist_eq_norm] at hn
  have hmδ : m * ‖y - q n‖ ≤ ε / 4 := by
    calc m * ‖y - q n‖ ≤ m * (ε / (4 * (m + 1))) := mul_le_mul_of_nonneg_left hn.le hm
      _ ≤ (m + 1) * (ε / (4 * (m + 1))) := by nlinarith
      _ = ε / 4 := by field_simp
  have a1 := abs_sub_le (g k y) (g k (q n)) (g' y)
  have a2 := abs_sub_le (g k (q n)) (g' (q n)) (g' y)
  have a3 : |g' (q n) - g' y| = |g' y - g' (q n)| := abs_sub_comm _ _
  linarith

theorem exists_countable_dense_H (d : ℕ) (m : ℝ) :
    ∃ 𝔉 : Set (Vec d → ℝ), 𝔉.Countable ∧ (∀ f ∈ 𝔉, InH m f) ∧
      ∀ f, InH m f → ∃ u : ℕ → Vec d → ℝ, (∀ k, u k ∈ 𝔉) ∧
        (∀ y, Tendsto (fun k => u k y) atTop (𝓝 (f y))) ∧
        (∀ j y, Tendsto (fun k => D1 (u k) j y) atTop (𝓝 (D1 f j y))) ∧
        ∀ i j y, Tendsto (fun k => D2 (u k) i j y) atTop (𝓝 (D2 f i j y)) := by
  obtain ⟨q, hq⟩ : ∃ q : ℕ → Vec d, DenseRange q := ⟨TopologicalSpace.denseSeq (Vec d),
    TopologicalSpace.denseRange_denseSeq (Vec d)⟩
  let E : (Vec d → ℝ) → (ℕ → ℝ × (Fin d → ℝ) × (Fin d → Fin d → ℝ)) := fun f n =>
    (f (q n), fun j => D1 f j (q n), fun i j => D2 f i j (q n))
  have hsep : TopologicalSpace.IsSeparable (E '' {f | InH m f}) :=
    TopologicalSpace.IsSeparable.of_separableSpace _
  obtain ⟨t, hts, htc, hSt⟩ := hsep.exists_countable_dense_subset
  have hex : ∀ z : t, ∃ f : Vec d → ℝ, InH m f ∧ E f = z.1 := fun z => hts z.2
  choose g hg using hex
  haveI : Countable t := htc.to_subtype
  refine ⟨Set.range g, Set.countable_range g, ?_, ?_⟩
  · rintro f ⟨z, rfl⟩
    exact (hg z).1
  · intro f hf
    have hmem : E f ∈ closure t := hSt ⟨f, hf, rfl⟩
    obtain ⟨x, hx, hxlim⟩ := mem_closure_iff_seq_limit.1 hmem
    have hcoord : ∀ (n : ℕ) (φ : (ℝ × (Fin d → ℝ) × (Fin d → Fin d → ℝ)) → ℝ),
        Continuous φ → Tendsto (fun k => φ (x k n)) atTop (𝓝 (φ (E f n))) :=
      fun n φ hφ => (hφ.tendsto _).comp (tendsto_pi_nhds.1 hxlim n)
    have hE : ∀ k n, E (g ⟨x k, hx k⟩) n = x k n := fun k n =>
      congrFun (hg ⟨x k, hx k⟩).2 n
    refine ⟨fun k => g ⟨x k, hx k⟩, fun k => ⟨_, rfl⟩, ?_, ?_, ?_⟩
    · intro y
      refine tendsto_of_dense_lipschitz (fun k => (hg ⟨x k, hx k⟩).1.2.1) hf.2.1 q hq
        (fun n => ?_) y
      refine Filter.Tendsto.congr (fun k => ?_) (hcoord n Prod.fst continuous_fst)
      exact (congrArg Prod.fst (hE k n)).symm
    · intro j y
      refine tendsto_of_dense_lipschitz (fun k => (hg ⟨x k, hx k⟩).1.2.2.1 j) (hf.2.2.1 j) q hq
        (fun n => ?_) y
      refine Filter.Tendsto.congr (fun k => ?_)
        (hcoord n (fun p => p.2.1 j) ((continuous_apply j).comp (continuous_fst.comp continuous_snd)))
      exact (congrArg (fun p => p.2.1 j) (hE k n)).symm
    · intro i j y
      refine tendsto_of_dense_lipschitz (fun k => (hg ⟨x k, hx k⟩).1.2.2.2 i j) (hf.2.2.2 i j)
        q hq (fun n => ?_) y
      refine Filter.Tendsto.congr (fun k => ?_)
        (hcoord n (fun p => p.2.2 i j)
          ((continuous_apply j).comp ((continuous_apply i).comp
            (continuous_snd.comp continuous_snd))))
      exact (congrArg (fun p => p.2.2 i j) (hE k n)).symm

/-- The countable test family. -/
theorem exists_countable_testFamily (d : ℕ) :
    ∃ 𝔉 : Set (Vec d → ℝ), 𝔉.Countable ∧
      (∀ f ∈ 𝔉, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f) ∧
      ∀ f : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
        ∃ (m : ℝ) (u : ℕ → Vec d → ℝ), (∀ k, u k ∈ 𝔉) ∧ (∀ k, InH m (u k)) ∧
          (∀ y, Tendsto (fun k => u k y) atTop (𝓝 (f y))) ∧
          (∀ j y, Tendsto (fun k => D1 (u k) j y) atTop (𝓝 (D1 f j y))) ∧
          ∀ i j y, Tendsto (fun k => D2 (u k) i j y) atTop (𝓝 (D2 f i j y)) := by
  choose 𝔉 hc hH hd using fun n : ℕ => exists_countable_dense_H d (n : ℝ)
  refine ⟨⋃ n, 𝔉 n, Set.countable_iUnion hc, ?_, ?_⟩
  · intro f hf
    obtain ⟨n, hn⟩ := Set.mem_iUnion.1 hf
    exact (hH n f hn).1
  · intro f hf hcf
    obtain ⟨m, hm⟩ := exists_inH hf hcf
    obtain ⟨n, hn⟩ := exists_nat_ge m
    have hmn : InH (n : ℝ) f := by
      obtain ⟨h1, h2, h3, h4⟩ := hm
      exact ⟨h1, h2.mono hn, fun j => (h3 j).mono hn, fun i j => (h4 i j).mono hn⟩
    obtain ⟨u, hu, h1, h2, h3⟩ := hd n f hmn
    exact ⟨n, u, fun k => Set.mem_iUnion.2 ⟨n, hu k⟩, fun k => hH n _ (hu k), h1, h2, h3⟩

end EinsteinFull
