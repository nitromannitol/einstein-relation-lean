import EinsteinFull.Calculus.CLTwoSidedProcess

/-!
# Finite-dimensional laws of the two-sided environment process

On a time grid `hℤ`, the product of bounded observables at consecutive grid times starting at a
grid time integrates under the two-sided law to the multi-time kernel mean of the same list
started from the environment law (`integral_tsGridProd`). The value depends only on the list,
so it is unchanged by grid time shifts, and it is unchanged by reversing the list, which is the
reflection of the times.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinFull EinsteinRelation

variable {d : ℕ}

/-- The last observable met when a backward list is read from time zero. -/
def lastObs : List (ℝ≥0 × (FieldPair d → ℝ)) → (FieldPair d → ℝ) → (FieldPair d → ℝ)
  | [], g => g
  | (_, f) :: L, _ => lastObs L f

/-- The forward list obtained by reading a backward list from its far end. -/
def revAcc : List (ℝ≥0 × (FieldPair d → ℝ)) → (FieldPair d → ℝ) →
    List (ℝ≥0 × (FieldPair d → ℝ)) → List (ℝ≥0 × (FieldPair d → ℝ))
  | [], _, Lf => Lf
  | (s, f) :: L, g, Lf => revAcc L f ((s, g) :: Lf)

/-- The left-nested kernel mean of a backward list, with a forward chain mean at time zero, is the
right-nested kernel mean from the far end. -/
theorem leftAcc_mul_chainMean (K : Kernel (FieldPair d × Vec d) (Path d)) :
    ∀ (Lb : List (ℝ≥0 × (FieldPair d → ℝ))) (g : FieldPair d → ℝ)
      (Lf : List (ℝ≥0 × (FieldPair d → ℝ))),
      leftAcc K (fun ω => g ω * chainMean K Lf ω) Lb =
        fun ω => lastObs Lb g ω * chainMean K (revAcc Lb g Lf) ω
  | [], _, _ => rfl
  | (s, f) :: L, g, Lf => by
    simp only [leftAcc, lastObs, revAcc]
    exact leftAcc_mul_chainMean K L f ((s, g) :: Lf)

/-- Uniform gaps. -/
def gridGaps (h : ℝ≥0) (L : List (FieldPair d → ℝ)) : List (ℝ≥0 × (FieldPair d → ℝ)) :=
  L.map fun f => (h, f)

/-- The observable list read backwards. -/
def revAccObs : List (FieldPair d → ℝ) → (FieldPair d → ℝ) → List (FieldPair d → ℝ) →
    List (FieldPair d → ℝ)
  | [], _, A => A
  | f :: L, g, A => revAccObs L f (g :: A)

theorem lastObs_cons_revAccObs (h : ℝ≥0) :
    ∀ (L : List (FieldPair d → ℝ)) (g : FieldPair d → ℝ) (A : List (FieldPair d → ℝ)),
      lastObs (gridGaps h L) g :: revAccObs L g A = (g :: L).reverse ++ A
  | [], _, _ => rfl
  | f :: L, g, A => by
    simp only [gridGaps, List.map_cons, lastObs, revAccObs]
    rw [show lastObs (List.map (fun f => (h, f)) L) f = lastObs (gridGaps h L) f from rfl,
      lastObs_cons_revAccObs h L f (g :: A)]
    simp

theorem revAcc_gridGaps (h : ℝ≥0) :
    ∀ (L : List (FieldPair d → ℝ)) (g : FieldPair d → ℝ) (A : List (FieldPair d → ℝ)),
      revAcc (gridGaps h L) g (gridGaps h A) = gridGaps h (revAccObs L g A)
  | [], _, _ => rfl
  | f :: L, g, A => by
    simp only [gridGaps, List.map_cons, revAcc, revAccObs]
    exact revAcc_gridGaps h L f (g :: A)

/-- Product of observables at the grid times `t, t + h, t + 2h, …`. -/
def tsGridProd (h : ℝ≥0) : ℝ → List (FieldPair d → ℝ) → TwoSidedSpace d → ℝ
  | _, [], _ => 1
  | t, f :: L, ω => f (tsState t ω) * tsGridProd h (t + h) L ω

/-- Product of observables at the grid times `t, t - h, t - 2h, …`. -/
def tsGridProdBwd (h : ℝ≥0) : ℝ → List (FieldPair d → ℝ) → TwoSidedSpace d → ℝ
  | _, [], _ => 1
  | t, f :: L, ω => f (tsState t ω) * tsGridProdBwd h (t - h) L ω

theorem tsGridProd_eq_tsFwdProd (h : ℝ≥0) :
    ∀ (L : List (FieldPair d → ℝ)) (t : ℝ) (ω : TwoSidedSpace d),
      tsGridProd h (t + h) L ω = tsFwdProd (gridGaps h L) t ω
  | [], _, _ => rfl
  | f :: L, t, ω => by
    simp only [tsGridProd, gridGaps, List.map_cons, tsFwdProd]
    rw [tsGridProd_eq_tsFwdProd h L (t + h) ω]
    rfl

theorem tsGridProdBwd_eq_tsBwdProd (h : ℝ≥0) :
    ∀ (L : List (FieldPair d → ℝ)) (t : ℝ) (ω : TwoSidedSpace d),
      tsGridProdBwd h (t - h) L ω = tsBwdProd (gridGaps h L) t ω
  | [], _, _ => rfl
  | f :: L, t, ω => by
    simp only [tsGridProdBwd, gridGaps, List.map_cons, tsBwdProd]
    rw [tsGridProdBwd_eq_tsBwdProd h L (t - h) ω]
    rfl

theorem tsGridProd_append (h : ℝ≥0) :
    ∀ (L₁ L₂ : List (FieldPair d → ℝ)) (t : ℝ) (ω : TwoSidedSpace d),
      tsGridProd h t (L₁ ++ L₂) ω =
        tsGridProd h t L₁ ω * tsGridProd h (t + L₁.length * h) L₂ ω
  | [], L₂, t, ω => by simp [tsGridProd]
  | f :: L₁, L₂, t, ω => by
    simp only [List.cons_append, tsGridProd, List.length_cons]
    rw [tsGridProd_append h L₁ L₂ (t + h) ω]
    push_cast
    rw [show t + h + L₁.length * h = t + (L₁.length + 1) * h by ring]
    ring

theorem tsGridProd_reverse (h : ℝ≥0) :
    ∀ (L : List (FieldPair d → ℝ)) (t : ℝ) (ω : TwoSidedSpace d),
      tsGridProd h t L.reverse ω = tsGridProdBwd h (t + L.length * h - h) L ω
  | [], _, _ => rfl
  | f :: L, t, ω => by
    rw [List.reverse_cons, tsGridProd_append, tsGridProd_reverse h L t ω, List.length_reverse]
    simp only [tsGridProd, tsGridProdBwd, List.length_cons, mul_one]
    push_cast
    rw [show t + (L.length + 1) * h - h = t + L.length * h by ring,
      show t + L.length * h - h = t + (L.length + 1) * h - h - h by ring]
    ring

theorem tsGridProd_shift (h : ℝ≥0) :
    ∀ (L : List (FieldPair d → ℝ)) (t τ : ℝ) (ω : TwoSidedSpace d),
      tsGridProd h t L (tsShift τ ω) = tsGridProd h (t + τ) L ω
  | [], _, _, _ => rfl
  | f :: L, t, τ, ω => by
    simp only [tsGridProd, tsState_shift]
    rw [tsGridProd_shift h L (t + h) τ ω, show t + h + τ = t + τ + h by ring]

theorem tsGridProd_refl (h : ℝ≥0) :
    ∀ (L : List (FieldPair d → ℝ)) (t τ : ℝ) (ω : TwoSidedSpace d),
      tsGridProd h t L (tsRefl τ ω) = tsGridProdBwd h (2 * τ - t) L ω
  | [], _, _, _ => rfl
  | f :: L, t, τ, ω => by
    simp only [tsGridProd, tsGridProdBwd, tsState_refl]
    rw [tsGridProd_refl h L (t + h) τ ω, show 2 * τ - (t + h) = 2 * τ - t - h by ring]

/-- The canonical value of an observable list: its multi-time kernel mean from the environment
law. -/
def gridCV (Q : Measure (FieldPair d)) (K : Kernel (FieldPair d × Vec d) (Path d)) (h : ℝ≥0) :
    List (FieldPair d → ℝ) → ℝ
  | [] => 1
  | f :: L => ∫ ω, f ω * chainMean K (gridGaps h L) ω ∂Q

theorem chainMean_gridGaps_append_one (K : Kernel (FieldPair d × Vec d) (Path d))
    [IsMarkovKernel K] (h : ℝ≥0) :
    ∀ L : List (FieldPair d → ℝ),
      chainMean K (gridGaps h (L ++ [fun _ => 1])) = chainMean K (gridGaps h L)
  | [] => by
    funext ω
    simp [gridGaps, chainMean, kernelPhysMean]
  | f :: L => by
    funext ω
    simp only [List.cons_append, gridGaps, List.map_cons, chainMean]
    have := chainMean_gridGaps_append_one K h L
    simp only [gridGaps] at this
    rw [this]

theorem gridCV_append_one (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : Kernel (FieldPair d × Vec d) (Path d)) [IsMarkovKernel K] (h : ℝ≥0) :
    ∀ L : List (FieldPair d → ℝ), gridCV Q K h (L ++ [fun _ => 1]) = gridCV Q K h L
  | [] => by simp [gridCV, gridGaps, chainMean]
  | f :: L => by
    simp only [List.cons_append, gridCV]
    rw [chainMean_gridGaps_append_one K h L]

theorem gridCV_append_ones (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : Kernel (FieldPair d × Vec d) (Path d)) [IsMarkovKernel K] (h : ℝ≥0)
    (L : List (FieldPair d → ℝ)) :
    ∀ n : ℕ, gridCV Q K h (L ++ List.replicate n (fun _ => 1)) = gridCV Q K h L
  | 0 => by simp
  | n + 1 => by
    rw [List.replicate_succ', ← List.append_assoc, gridCV_append_one,
      gridCV_append_ones Q K h L n]

theorem tsGridProd_ones (h : ℝ≥0) :
    ∀ (n : ℕ) (t : ℝ) (ω : TwoSidedSpace d),
      tsGridProd h t (List.replicate n (fun _ => (1 : ℝ))) ω = 1
  | 0, _, _ => rfl
  | n + 1, t, ω => by
    simp only [List.replicate_succ, tsGridProd, one_mul]
    exact tsGridProd_ones h n (t + h) ω

/-- Unit observables. -/
def IsUnitList (L : List (FieldPair d → ℝ)) : Prop := ∀ f ∈ L, Measurable f ∧ ∀ ω, |f ω| ≤ 1

theorem IsUnitList.gridGaps {h : ℝ≥0} {L : List (FieldPair d → ℝ)} (hL : IsUnitList L) :
    IsUnitObservables (gridGaps h L) := by
  intro p hp
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hp
  exact hL f hf

theorem IsUnitList.reverse {L : List (FieldPair d → ℝ)} (hL : IsUnitList L) :
    IsUnitList L.reverse := fun f hf => hL f (List.mem_reverse.1 hf)

section Annealed

variable (hd : 2 ≤ d) (D : StructuralData d)
  (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
  (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
  (hap : ∀ᵐ ω ∂Q.measure, ω ∈ aperiodicSet d)
  {K : Kernel (FieldPair d × Vec d) (Path d)} [IsMarkovKernel K]
  (hK : ∀ ω : FieldPair d, IsRegular D.ellipticity ω → ∀ x : Vec d,
    SolvesMartingaleProblem (External.Draft.svGenerator (reducedCoefficient ω)
      (forcedDrift (reducedCoefficient ω) (⟨0, by omega⟩ : Fin d) 0)) x (K (ω, x)))

include hQ hunforced hpath hK in
/-- The kernel mean preserves the environment law. -/
theorem integral_kernelPhysMean {g : FieldPair d → ℝ} (hg : Measurable g)
    (hgb : ∀ ω, |g ω| ≤ 1) (s : ℝ≥0) :
    ∫ ω, kernelPhysMean K g s ω ∂Q.measure = ∫ ω, g ω ∂Q.measure := by
  have h := kernelPhys_detailed_balance hd D Q hQ hunforced hpath hK (f := fun _ => 1)
    measurable_const hg (fun _ => by simp) hgb s
  have h1 : kernelPhysMean K (fun _ => (1 : ℝ)) s = fun _ => 1 := by
    funext ω
    simp [kernelPhysMean]
  simpa only [one_mul, h1, mul_one] using h

include hQ hunforced hpath hK in
/-- Reversing an observable list does not change its canonical value. -/
theorem gridCV_reverse (h : ℝ≥0) {L : List (FieldPair d → ℝ)} (hL : IsUnitList L) :
    gridCV Q.measure K h L.reverse = gridCV Q.measure K h L := by
  rcases L with _ | ⟨f, L⟩
  · rfl
  obtain ⟨hfm, hfb⟩ := hL f (List.mem_cons_self ..)
  have hL' : IsUnitList L := fun g hg => hL g (List.mem_cons_of_mem _ hg)
  have hrev := integral_mul_chainMean_eq_leftAcc hd D Q hQ hunforced hpath hK (gridGaps h L)
    hL'.gridGaps f hfm hfb
  have hla := leftAcc_mul_chainMean K (gridGaps h L) f []
  simp only [chainMean, mul_one] at hla
  rw [hla] at hrev
  have hlist := lastObs_cons_revAccObs h L f []
  rw [List.append_nil] at hlist
  rw [← hlist]
  simp only [gridCV]
  rw [hrev]
  congr 1
  funext ω
  rw [show (revAcc (gridGaps h L) f []) = revAcc (gridGaps h L) f (gridGaps h []) from rfl,
    revAcc_gridGaps]

include hQ hunforced hpath hap hK in
/-- Finite-dimensional laws of the two-sided process on a grid: the product of unit observables
at consecutive grid times from a grid time integrates to the canonical value of the list. -/
theorem integral_tsGridProd (h : ℝ≥0) (a : ℤ) {L : List (FieldPair d → ℝ)} (hL : IsUnitList L) :
    ∫ ω, tsGridProd h (a * h) L ω ∂tsLaw Q K = gridCV Q.measure K h L := by
  have := tsLaw_isProbability Q hap K
  -- the case of a list reaching time zero from a negative start
  have hcross : ∀ (n : ℕ) (M : List (FieldPair d → ℝ)), IsUnitList M → n < M.length →
      ∫ ω, tsGridProd h (-(n : ℝ) * h) M ω ∂tsLaw Q K = gridCV Q.measure K h M := by
    intro n M hM hn
    obtain ⟨f, L₂, hdrop⟩ : ∃ f L₂, M.drop n = f :: L₂ := by
      rcases hd' : M.drop n with _ | ⟨f, L₂⟩
      · rw [List.drop_eq_nil_iff] at hd'
        omega
      · exact ⟨f, L₂, rfl⟩
    set L₁ := M.take n with hL₁
    have hM' : M = L₁ ++ f :: L₂ := by rw [← hdrop, List.take_append_drop]
    have hlen : L₁.length = n := by rw [hL₁, List.length_take]; omega
    have hU₁ : IsUnitList L₁ := fun g hg => hM g (hM' ▸ List.mem_append_left _ hg)
    have hU₂ : IsUnitList L₂ := fun g hg => hM g (hM' ▸ List.mem_append_right _
      (List.mem_cons_of_mem _ hg))
    obtain ⟨hfm, hfb⟩ := hM f (hM' ▸ List.mem_append_right _ (List.mem_cons_self ..))
    have hsplit : ∀ ω, tsGridProd h (-(n : ℝ) * h) M ω =
        f (tsState 0 ω) * tsBwdProd (gridGaps h L₁.reverse) 0 ω *
          tsFwdProd (gridGaps h L₂) 0 ω := by
      intro ω
      rw [hM', tsGridProd_append, hlen]
      have h1 : tsGridProd h (-(n : ℝ) * h) L₁ ω = tsBwdProd (gridGaps h L₁.reverse) 0 ω := by
        rw [← List.reverse_reverse L₁, tsGridProd_reverse, List.reverse_reverse,
          List.length_reverse, hlen, ← tsGridProdBwd_eq_tsBwdProd]
        congr 1
        ring
      have h2 : tsGridProd h (-(n : ℝ) * h + n * h) (f :: L₂) ω =
          f (tsState 0 ω) * tsFwdProd (gridGaps h L₂) 0 ω := by
        rw [show -(n : ℝ) * h + n * h = 0 by ring]
        simp only [tsGridProd]
        rw [show (0 : ℝ) + h = 0 + h from rfl, tsGridProd_eq_tsFwdProd]
      rw [h1, h2]
      ring
    simp_rw [hsplit]
    rw [integral_tsLaw_split hd D Q hap hK hfm hfb hU₁.reverse.gridGaps hU₂.gridGaps]
    obtain ⟨hcm, hcb⟩ := chainMean_measurable_bound K (gridGaps h L₂) hU₂.gridGaps
    have hrev := integral_mul_chainMean_eq_leftAcc hd D Q hQ hunforced hpath hK
      (gridGaps h L₁.reverse) hU₁.reverse.gridGaps (fun ω => f ω * chainMean K (gridGaps h L₂) ω)
      (hfm.mul hcm) fun ω => by
        rw [abs_mul]
        exact (mul_le_mul (hfb ω) (hcb ω) (abs_nonneg _) zero_le_one).trans (by norm_num)
    rw [leftAcc_mul_chainMean] at hrev
    have hlist := lastObs_cons_revAccObs h L₁.reverse f L₂
    rw [List.reverse_cons, List.reverse_reverse, List.append_assoc, List.singleton_append,
      ← hM'] at hlist
    calc ∫ ω, f ω * chainMean K (gridGaps h L₁.reverse) ω * chainMean K (gridGaps h L₂) ω
          ∂Q.measure
        = ∫ ω, f ω * chainMean K (gridGaps h L₂) ω * chainMean K (gridGaps h L₁.reverse) ω
          ∂Q.measure := by congr 1; funext ω; ring
      _ = ∫ ω, lastObs (gridGaps h L₁.reverse) f ω *
            chainMean K (revAcc (gridGaps h L₁.reverse) f (gridGaps h L₂)) ω ∂Q.measure := hrev
      _ = gridCV Q.measure K h M := by
          rw [← hlist, revAcc_gridGaps]
          rfl
  rcases le_or_gt 0 a with ha | ha
  · -- a nonnegative start: a forward chain from time zero
    rcases L with _ | ⟨f, L⟩
    · simp [tsGridProd, gridCV]
    obtain ⟨hfm, hfb⟩ := hL f (List.mem_cons_self ..)
    have hL' : IsUnitList L := fun g hg => hL g (List.mem_cons_of_mem _ hg)
    let s : ℝ≥0 := (a.toNat : ℝ≥0) * h
    have hs : ((s : ℝ)) = a * h := by
      simp only [s, NNReal.coe_mul, NNReal.coe_natCast]
      rw [show ((a.toNat : ℕ) : ℝ) = (a : ℝ) by exact_mod_cast Int.toNat_of_nonneg ha]
    have hsplit : ∀ ω, tsGridProd h (a * h) (f :: L) ω =
        (fun _ => (1 : ℝ)) (tsState 0 ω) * tsBwdProd [] 0 ω *
          tsFwdProd ((s, f) :: gridGaps h L) 0 ω := by
      intro ω
      simp only [tsGridProd, tsBwdProd, tsFwdProd, one_mul, zero_add, hs]
      rw [← tsGridProd_eq_tsFwdProd]
    simp_rw [hsplit]
    have hLf : IsUnitObservables ((s, f) :: gridGaps h L) := by
      intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact ⟨hfm, hfb⟩
      · exact hL'.gridGaps p hp
    rw [integral_tsLaw_split hd D Q hap hK measurable_const (fun _ => by simp)
      (fun _ h => (List.not_mem_nil h).elim) hLf]
    obtain ⟨hcm, hcb⟩ := chainMean_measurable_bound K (gridGaps h L) hL'.gridGaps
    simp only [chainMean, one_mul, gridCV]
    exact integral_kernelPhysMean hd D Q hQ hunforced hpath hK (hfm.mul hcm) (fun ω => by
      rw [Pi.mul_apply, abs_mul]
      exact (mul_le_mul (hfb ω) (hcb ω) (abs_nonneg _) zero_le_one).trans (by norm_num)) s
  · -- a negative start: pad with unit observables until the list reaches time zero
    set n : ℕ := (-a).toNat with hn
    have han : (a : ℝ) = -(n : ℝ) := by
      rw [hn]
      have : ((-a).toNat : ℤ) = -a := Int.toNat_of_nonneg (by omega)
      exact_mod_cast (by omega : a = -((-a).toNat : ℤ))
    let M := L ++ List.replicate (n + 1) (fun _ => (1 : ℝ))
    have hM : IsUnitList M := by
      intro g hg
      rcases List.mem_append.1 hg with hg | hg
      · exact hL g hg
      · rw [List.eq_of_mem_replicate hg]
        exact ⟨measurable_const, fun _ => by simp⟩
    have hlenM : n < M.length := by simp [M]; omega
    have hprod : ∀ ω, tsGridProd h (a * h) L ω = tsGridProd h (-(n : ℝ) * h) M ω := by
      intro ω
      rw [tsGridProd_append, tsGridProd_ones, mul_one, han]
    simp_rw [hprod]
    rw [hcross n M hM hlenM]
    exact gridCV_append_ones Q.measure K h L (n + 1)

end Annealed

end EinsteinFull.Blueprint
