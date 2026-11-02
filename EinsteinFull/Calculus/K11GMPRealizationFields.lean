import EinsteinFull.Calculus.C8FoundationGMPAssociation

/-! # Derivable fields of the fixed-environment realization

For the physical `C₀` kernel semigroup `gmpPhysicalC0KernelSemigroup` and its continuous-path
law, this file proves the fields of `GantertFixedEnvironmentRealization` that follow from the
semigroup structure and from `gmpPhysicalC0KernelSemigroup_existsUnique_continuous_realization`:
the Markov and semigroup properties of the transition kernels, and the Markov, starting-point,
one-time-marginal and ordered finite-dimensional properties of the path law.  The heat-kernel
density, reversibility and the closed-form identification are not addressed here.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

noncomputable section

namespace EinsteinFull.Blueprint

open EinsteinRelation EinsteinRelation.External.GantertSection7Support MarkovProcess
open MarkovProcess.SubMarkovKernelSemigroup

theorem k11_fdd_finset {d : ℕ} (P : SubMarkovKernelSemigroup (Vec d))
    (K : Kernel (Vec d) (Path d))
    (hK : ∀ I : Finset ℝ≥0, K.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I)
    (J : Finset ℝ≥0) (x : Vec d) :
    (K x).map (fun γ (i : Fin J.card) => γ (finiteSetTimes J i)) =
      finiteTimeKernel P (finiteSetTimes J) x := by
  have h1 := congrArg (fun κ => κ x) (hK J)
  simp only [finiteSetKernel_eq_map] at h1
  rw [Kernel.map_apply _ (ContinuousPath.measurable_finiteEvaluation _),
    Kernel.map_apply _ (measurable_orderedPathToFiniteSet J)] at h1
  have hm : Measurable (fun (f : J → Vec d) (i : Fin J.card) =>
      f ((J.orderIsoOfFin rfl) i)) :=
    measurable_pi_iff.mpr fun i => measurable_pi_apply _
  have h2 := congrArg (Measure.map (fun (f : J → Vec d) (i : Fin J.card) =>
      f ((J.orderIsoOfFin rfl) i))) h1
  rw [Measure.map_map hm (ContinuousPath.measurable_finiteEvaluation _),
    Measure.map_map hm (measurable_orderedPathToFiniteSet J)] at h2
  have e1 : ((fun (f : J → Vec d) (i : Fin J.card) => f ((J.orderIsoOfFin rfl) i)) ∘
      orderedPathToFiniteSet J) = id := by
    funext p i
    simp [orderedPathToFiniteSet]
  rw [e1, Measure.map_id] at h2
  rw [← h2]
  congr 1

theorem k11_integral_finiteTimeKernel_succ {d n : ℕ} (P : SubMarkovKernelSemigroup (Vec d))
    (hP : P.IsConservative) (times : FiniteOrderedTimes (n + 1)) (x : Vec d)
    (G : (Fin (n + 1) → Vec d) → ℝ) (hG : Measurable G) (B : ℝ) (hB : ∀ p, |G p| ≤ B) :
    ∫ p, G p ∂finiteTimeKernel P times x =
      ∫ y, ∫ p, G (Fin.cons y p) ∂finiteTimeKernel P times.relativeTail y ∂P (times 0) x := by
  have := hP.isMarkovKernel (times 0)
  have := hP.isMarkovKernel_finiteTimeKernel P times.relativeTail
  have hc : Measurable (fun z : Vec d × (Fin n → Vec d) =>
      @Fin.cons n (fun _ : Fin (n + 1) => Vec d) z.1 z.2) := measurable_finCons
  rw [finiteTimeKernel_succ, Kernel.mapOfMeasurable_eq_map, Kernel.map_apply _ hc,
    integral_map hc.aemeasurable hG.aestronglyMeasurable]
  have hint : Integrable (fun z : Vec d × (Fin n → Vec d) =>
      G (@Fin.cons n (fun _ : Fin (n + 1) => Vec d) z.1 z.2))
      ((P (times 0) ⊗ₖ Kernel.prodMkLeft (Vec d) (finiteTimeKernel P times.relativeTail)) x) :=
    Integrable.of_bound (hG.comp hc).aestronglyMeasurable B
      (Filter.Eventually.of_forall fun z => by simpa using hB _)
  rw [ProbabilityTheory.integral_compProd hint]
  simp [Kernel.prodMkLeft_apply]

/-- The cumulative times `t, t + g₁, t + g₁ + g₂, …` of a first time and a list of gaps, as a
finite coordinate family. -/
def k11TimeFun : ℝ≥0 → (gs : List ℝ≥0) → Fin (gs.length + 1) → ℝ≥0
  | t, [] => fun _ => t
  | t, g :: gs => Fin.cons t (fun i => t + k11TimeFun g gs i)

theorem k11TimeFun_zero (t : ℝ≥0) (gs : List ℝ≥0) : k11TimeFun t gs 0 = t := by
  cases gs <;> rfl

theorem k11TimeFun_ge (t : ℝ≥0) (gs : List ℝ≥0) (i : Fin (gs.length + 1)) :
    t ≤ k11TimeFun t gs i := by
  induction gs generalizing t with
  | nil => exact le_rfl
  | cons g gs ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · exact le_of_eq (k11TimeFun_zero t _).symm
      · simp only [k11TimeFun, Fin.cons_succ]
        exact le_self_add

theorem k11TimeFun_strictMono (t : ℝ≥0) (gs : List ℝ≥0) (h : ∀ g ∈ gs, 0 < g) :
    StrictMono (k11TimeFun t gs) := by
  induction gs generalizing t with
  | nil =>
      intro i j hij
      exfalso
      have hi := i.2
      have hj := j.2
      have := Fin.lt_def.mp hij
      simp only [List.length_nil] at hi hj
      omega
  | cons g gs ih =>
      have hg : 0 < g := h g (by simp)
      have ih' := ih g (fun g' hg' => h g' (by simp [hg']))
      change StrictMono (Matrix.vecCons t (fun i => t + k11TimeFun g gs i))
      rw [strictMono_vecCons]
      refine ⟨?_, fun i j hij => ?_⟩
      · simp only [k11TimeFun_zero]
        exact lt_add_of_pos_right t hg
      · exact (add_lt_add_iff_left t).2 (ih' hij)

/-- The strictly increasing time family attached to a first time and positive gaps. -/
def k11Times (t : ℝ≥0) (gs : List ℝ≥0) (h : ∀ g ∈ gs, 0 < g) :
    FiniteOrderedTimes (gs.length + 1) :=
  OrderEmbedding.ofStrictMono (k11TimeFun t gs) (k11TimeFun_strictMono t gs h)

theorem k11Times_relativeTail (t g : ℝ≥0) (gs : List ℝ≥0) (h : ∀ g' ∈ g :: gs, 0 < g') :
    (k11Times t (g :: gs) h).relativeTail =
      k11Times g gs (fun g' hg' => h g' (by simp [hg'])) := by
  apply DFunLike.ext _ _
  intro i
  change k11TimeFun t (g :: gs) i.succ - k11TimeFun t (g :: gs) 0 = k11TimeFun g gs i
  simp [k11TimeFun]

theorem k11TimeFun_ofFn (s : ℝ≥0) (t : ℝ≥0) (gs : List ℝ≥0) {d : ℕ} (γ : Path d) :
    List.ofFn (fun i => pathPosition (s + k11TimeFun t gs i) γ) =
      pathPositionsAtTimes (cumulativeTimesFrom s (t :: gs)) γ := by
  induction gs generalizing s t with
  | nil => simp [k11TimeFun, cumulativeTimesFrom, pathPositionsAtTimes]
  | cons g gs ih =>
      have e : List.ofFn (fun i : Fin ((g :: gs).length + 1) =>
          pathPosition (s + k11TimeFun t (g :: gs) i) γ) =
          pathPosition (s + t) γ :: List.ofFn (fun i : Fin (gs.length + 1) =>
            pathPosition (s + t + k11TimeFun g gs i) γ) := by
        rw [List.ofFn_succ]
        congr 1
        simp only [k11TimeFun, Fin.cons_succ, add_assoc]
        rfl
      rw [e, ih (s + t) g]
      rfl

theorem k11_measurable_ofFn {d : ℕ} : ∀ n : ℕ, Measurable (fun p : Fin n → Vec d => List.ofFn p)
  | 0 => by simp only [List.ofFn_zero]; exact (measurable_const : Measurable fun _ : Fin 0 → Vec d => ([] : List (Vec d)))
  | n + 1 => by
      have ih := k11_measurable_ofFn (d := d) n
      have h1 : Measurable (fun (p : Fin (n + 1) → Vec d) (i : Fin n) => p i.succ) :=
        Measurable.of_eval fun i => measurable_pi_apply i.succ
      simp only [List.ofFn_succ]
      have h2 : Measurable (fun p : Fin (n + 1) → Vec d =>
          (p 0, List.ofFn (fun i : Fin n => p i.succ))) :=
        (measurable_pi_apply 0).prodMk (ih.comp h1)
      exact List.continuous_cons.measurable.comp h2

theorem k11_fdd_times {d : ℕ} (P : SubMarkovKernelSemigroup (Vec d))
    (K : Kernel (Vec d) (Path d))
    (hK : ∀ I : Finset ℝ≥0, K.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I)
    {n : ℕ} (times : FiniteOrderedTimes n) (x : Vec d) :
    (K x).map (fun γ (i : Fin n) => γ (times i)) = finiteTimeKernel P times x := by
  have key : ∀ (J : Finset ℝ≥0) (m : ℕ) (hc : J.card = m) (t : FiniteOrderedTimes m),
      (∀ i, t i ∈ J) → (K x).map (fun γ (i : Fin m) => γ (t i)) = finiteTimeKernel P t x := by
    intro J m hc t ht
    subst hc
    have : t = finiteSetTimes J := Finset.orderEmbOfFin_unique' rfl ht
    rw [this]
    exact k11_fdd_finset P K hK J x
  exact key (Finset.univ.map times.toEmbedding) n (by simp) times (by simp)

theorem k11_strict_fin {d : ℕ} (P : SubMarkovKernelSemigroup (Vec d)) (hP : P.IsConservative) :
    ∀ (gs : List ℝ≥0) (t : ℝ≥0) (h : ∀ g ∈ gs, 0 < g) (x : Vec d)
      (F : List (Vec d) → ℝ),
      Measurable (fun p : Fin (gs.length + 1) → Vec d => F (List.ofFn p)) → ∀ B : ℝ, (∀ l, |F l| ≤ B) →
      ∫ p, F (List.ofFn p) ∂finiteTimeKernel P (k11Times t gs h) x =
        iteratedMarkovCylinderIntegral (fun s => P s) (t :: gs) F x := by
  intro gs
  induction gs with
  | nil =>
      intro t h x F hF B hB
      rw [k11_integral_finiteTimeKernel_succ P hP _ x (fun p => F (List.ofFn p))
        hF B (fun p => hB _)]
      have h0 : k11Times t [] h 0 = t := k11TimeFun_zero t []
      rw [h0]
      simp [iteratedMarkovCylinderIntegral]
  | cons g gs ih =>
      intro t h x F hF B hB
      rw [k11_integral_finiteTimeKernel_succ P hP _ x (fun p => F (List.ofFn p))
        hF B (fun p => hB _)]
      have h0 : k11Times t (g :: gs) h 0 = t := k11TimeFun_zero t _
      rw [h0, k11Times_relativeTail]
      rw [iteratedMarkovCylinderIntegral]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      have := ih g (fun g' hg' => h g' (by simp [hg'])) y (fun l => F (y :: l))
        (by
          have hc : Measurable (fun p : Fin (gs.length + 1) → Vec d =>
              (Fin.cons y p : Fin (gs.length + 1 + 1) → Vec d)) := by
            refine measurable_pi_iff.mpr fun i => ?_
            refine Fin.cases ?_ (fun j => ?_) i
            · simp
            · simpa using measurable_pi_apply j
          have := hF.comp hc
          convert this using 1
          funext p
          simp only [Function.comp]
          rw [List.ofFn_cons])
        B (fun l => hB _)
      beta_reduce
      rw [← this]
      refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      simp [List.ofFn_succ]

/-- Duplicate the previous coordinate at each zero gap and otherwise consume the next
coordinate of the list of positions at the nonzero gaps. -/
noncomputable def k11Expand {d : ℕ} : Vec d → List ℝ≥0 → List (Vec d) → List (Vec d)
  | _, [], _ => []
  | prev, g :: gs, l =>
      if g = 0 then prev :: k11Expand prev gs l
      else match l with
        | [] => []
        | y :: l' => y :: k11Expand y gs l'

theorem k11_pos_expand {d : ℕ} (γ : Path d) : ∀ (gs : List ℝ≥0) (s : ℝ≥0),
    pathPositionsAtTimes (cumulativeTimesFrom s gs) γ =
      k11Expand (pathPosition s γ) gs
        (pathPositionsAtTimes (cumulativeTimesFrom s (gs.filter (fun g => g ≠ 0))) γ)
  | [], s => by simp [cumulativeTimesFrom, pathPositionsAtTimes, k11Expand]
  | g :: gs, s => by
      by_cases hg : g = 0
      · subst hg
        have := k11_pos_expand γ gs s
        simp only [cumulativeTimesFrom, pathPositionsAtTimes, List.map_cons, add_zero,
          List.filter_cons, k11Expand, ne_eq, not_true_eq_false, decide_false,
          Bool.false_eq_true, ite_false, ite_true] at this ⊢
        rw [this]
      · have := k11_pos_expand γ gs (s + g)
        simp only [cumulativeTimesFrom, pathPositionsAtTimes, List.map_cons,
          List.filter_cons, k11Expand, ne_eq, hg, not_false_eq_true, decide_true,
          ite_true] at this ⊢
        rw [this]
        simp

theorem k11_iter_expand {d : ℕ} (P : SubMarkovKernelSemigroup (Vec d)) :
    ∀ (gs : List ℝ≥0) (y : Vec d) (F : List (Vec d) → ℝ),
      iteratedMarkovCylinderIntegral (fun s => P s) gs F y =
        iteratedMarkovCylinderIntegral (fun s => P s) (gs.filter (fun g => g ≠ 0))
          (fun l => F (k11Expand y gs l)) y
  | [], y, F => by simp [iteratedMarkovCylinderIntegral, k11Expand]
  | g :: gs, y, F => by
      by_cases hg : g = 0
      · subst hg
        have h0 : P 0 y = Measure.dirac y := by
          show P.kernel 0 y = _
          rw [P.kernel_zero, Kernel.id_apply]
        have hf : ((0 : ℝ≥0) :: gs).filter (fun g => g ≠ 0) = gs.filter (fun g => g ≠ 0) := by
          simp
        rw [hf, iteratedMarkovCylinderIntegral, h0, integral_dirac,
          k11_iter_expand P gs y (fun l => F (y :: l))]
        simp [k11Expand]
      · have hf : (g :: gs).filter (fun g => g ≠ 0) = g :: gs.filter (fun g => g ≠ 0) := by
          simp [hg]
        rw [hf, iteratedMarkovCylinderIntegral, iteratedMarkovCylinderIntegral]
        refine integral_congr_ae (Filter.Eventually.of_forall fun y' => ?_)
        beta_reduce
        rw [k11_iter_expand P gs y' (fun l => F (y' :: l))]
        congr 1
        funext l
        simp [k11Expand, hg]

theorem k11_measurable_expand {d : ℕ} (gs : List ℝ≥0) : ∀ n : ℕ,
    Measurable (fun q : Vec d × (Fin n → Vec d) => k11Expand q.1 gs (List.ofFn q.2)) := by
  induction gs with
  | nil => intro n; simp only [k11Expand]; exact measurable_const
  | cons g gs ih =>
      intro n
      by_cases hg : g = 0
      · simp only [k11Expand, hg, ite_true]
        have h2 : Measurable (fun q : Vec d × (Fin n → Vec d) =>
            (q.1, k11Expand q.1 gs (List.ofFn q.2))) := measurable_fst.prodMk (ih n)
        exact List.continuous_cons.measurable.comp h2
      · cases n with
        | zero => simp only [k11Expand, hg, ite_false, List.ofFn_zero]; exact measurable_const
        | succ k =>
            simp only [k11Expand, hg, ite_false, List.ofFn_succ]
            have h1 : Measurable (fun q : Vec d × (Fin (k + 1) → Vec d) =>
                (q.2 0, fun i : Fin k => q.2 i.succ)) :=
              ((measurable_pi_apply 0).comp measurable_snd).prodMk
                (Measurable.of_eval fun i => (measurable_pi_apply i.succ).comp measurable_snd)
            have h2 : Measurable (fun q : Vec d × (Fin (k + 1) → Vec d) =>
                (q.2 0, k11Expand (q.2 0) gs (List.ofFn (fun i : Fin k => q.2 i.succ)))) :=
              ((measurable_pi_apply 0).comp measurable_snd).prodMk ((ih k).comp h1)
            exact List.continuous_cons.measurable.comp h2

theorem k11_strict_path {d : ℕ} (P : SubMarkovKernelSemigroup (Vec d)) (hP : P.IsConservative)
    (K : Kernel (Vec d) (Path d))
    (hK : ∀ I : Finset ℝ≥0, K.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I)
    (t : ℝ≥0) (gs : List ℝ≥0) (h : ∀ g ∈ gs, 0 < g) (x : Vec d) (F : List (Vec d) → ℝ)
    (hF : Measurable (fun p : Fin (gs.length + 1) → Vec d => F (List.ofFn p))) (B : ℝ)
    (hB : ∀ l, |F l| ≤ B) :
    ∫ γ, F (pathPositionsAtTimes (cumulativeTimes (t :: gs)) γ) ∂K x =
      iteratedMarkovCylinderIntegral (fun s => P s) (t :: gs) F x := by
  have hev : Measurable (fun (γ : Path d) (i : Fin (gs.length + 1)) => γ (k11Times t gs h i)) :=
    Measurable.of_eval fun i => measurable_pathPosition _
  have e1 : ∀ γ : Path d, pathPositionsAtTimes (cumulativeTimes (t :: gs)) γ =
      List.ofFn (fun i : Fin (gs.length + 1) => γ (k11Times t gs h i)) := by
    intro γ
    have := k11TimeFun_ofFn 0 t gs γ
    simp only [zero_add] at this
    exact this.symm
  simp_rw [e1]
  rw [← integral_map hev.aemeasurable hF.aestronglyMeasurable (μ := K x)
    (f := fun p : Fin (gs.length + 1) → Vec d => F (List.ofFn p)),
    k11_fdd_times P K hK, k11_strict_fin P hP gs t h x F hF B hB]

theorem k11_endpoint {d : ℕ} (P : SubMarkovKernelSemigroup (Vec d))
    (K : Kernel (Vec d) (Path d))
    (hK : ∀ I : Finset ℝ≥0, K.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I)
    (t : ℝ≥0) (x : Vec d) : (K x).map (pathPosition t) = P t x := by
  let T : FiniteOrderedTimes 1 := k11Times t [] (by simp)
  have hev : Measurable (fun (γ : Path d) (i : Fin 1) => γ (T i)) :=
    Measurable.of_eval fun i => measurable_pathPosition _
  have h := k11_fdd_times P K hK T x
  have h2 := congrArg (Measure.map (fun p : Fin 1 → Vec d => p 0)) h
  rw [Measure.map_map (measurable_pi_apply 0) hev] at h2
  have h3 : (finiteTimeKernel P T).map (fun p : Fin 1 → Vec d => p 0) = P (T 0) :=
    finiteTimeKernel_one_map_eval P T
  have h4 : ((finiteTimeKernel P T) x).map (fun p : Fin 1 → Vec d => p 0) = P (T 0) x := by
    rw [← Kernel.map_apply _ (measurable_pi_apply 0), h3]
  have h5 : T 0 = t := k11TimeFun_zero t []
  rw [h5] at h4
  rw [← h4, ← h2]
  rfl

theorem k11_starts_at {d : ℕ} (P : SubMarkovKernelSemigroup (Vec d))
    (K : Kernel (Vec d) (Path d))
    (hK : ∀ I : Finset ℝ≥0, K.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I)
    (x : Vec d) : ∀ᵐ γ ∂K x, pathPosition 0 γ = x := by
  have h := k11_endpoint P K hK 0 x
  have h0 : P 0 x = Measure.dirac x := by
    show P.kernel 0 x = _
    rw [P.kernel_zero, Kernel.id_apply]
  rw [h0] at h
  rw [ae_iff]
  have hm : MeasurableSet {y : Vec d | ¬ y = x} := (measurableSet_singleton x).compl
  have := congrArg (fun μ => μ {y : Vec d | ¬ y = x}) h
  simp only [Measure.map_apply (measurable_pathPosition 0) hm] at this
  simpa [Measure.dirac_apply' _ hm] using this

theorem k11_fdd_general {d : ℕ} (P : SubMarkovKernelSemigroup (Vec d)) (hP : P.IsConservative)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ I : Finset ℝ≥0, K.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I)
    (u : List ℝ≥0) (x : Vec d) (F : List (Vec d) → ℝ) (hF : Measurable F) (B : ℝ)
    (hB : ∀ l, |F l| ≤ B) :
    ∫ γ, F (pathPositionsAtTimes (cumulativeTimes u) γ) ∂K x =
      iteratedMarkovCylinderIntegral (fun s => P s) u F x := by
  have hae : ∀ᵐ γ ∂K x, pathPositionsAtTimes (cumulativeTimes u) γ =
      k11Expand x u (pathPositionsAtTimes
        (cumulativeTimes (u.filter (fun g => g ≠ 0))) γ) := by
    filter_upwards [k11_starts_at P K hK x] with γ hγ
    have := k11_pos_expand γ u 0
    rw [hγ] at this
    exact this
  rw [integral_congr_ae (hae.mono fun γ hγ => by rw [hγ]), k11_iter_expand P u x F]
  have hpos : ∀ g ∈ u.filter (fun g => g ≠ 0), 0 < g := fun g hg => by
    have := (List.mem_filter.mp hg).2
    simpa [pos_iff_ne_zero] using this
  generalize u.filter (fun g => g ≠ 0) = v at hpos ⊢
  rcases v with _ | ⟨h, hs⟩
  · simp [cumulativeTimes, cumulativeTimesFrom, pathPositionsAtTimes, iteratedMarkovCylinderIntegral]
  · refine k11_strict_path P hP K hK h hs (fun g hg => hpos g (by simp [hg])) x
      (fun l => F (k11Expand x u l)) ?_ B (fun l => hB _)
    exact hF.comp ((k11_measurable_expand u _).comp (measurable_const.prodMk measurable_id))

/-! ### The physical semigroup and its continuous-path law -/

/-- The transition kernels of the physical `C₀` kernel semigroup, as the time-indexed family of
kernels of `GantertFixedEnvironmentRealization`. -/
noncomputable def gmpPhysicalTransitionKernel {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) :
    ℝ≥0 → Kernel (Vec d) (Vec d) :=
  fun t => gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t

/-- The continuous-path law attached to the physical `C₀` kernel semigroup: the Markov kernel
into continuous paths with the finite-dimensional distributions of the semigroup, whose
existence and uniqueness is
`gmpPhysicalC0KernelSemigroup_existsUnique_continuous_realization`. -/
noncomputable def gmpPhysicalPathLaw {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) :
    Kernel (Vec d) (Path d) :=
  (gmpPhysicalC0KernelSemigroup_existsUnique_continuous_realization hd ω lam Λ hΛ hω
    hSmooth).exists.choose

/-- The defining property of the physical path law. -/
theorem gmpPhysicalPathLaw_spec {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) :
    IsMarkovKernel (gmpPhysicalPathLaw hd ω lam Λ hΛ hω hSmooth) ∧ ∀ I : Finset ℝ≥0,
      (gmpPhysicalPathLaw hd ω lam Λ hΛ hω hSmooth).map (ContinuousPath.finsetEvaluation I) =
        finiteSetKernel (gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth) I :=
  (gmpPhysicalC0KernelSemigroup_existsUnique_continuous_realization hd ω lam Λ hΛ hω
    hSmooth).exists.choose_spec

/-- Field `pathLaw_isMarkovKernel` for the physical realization. -/
theorem gmpPhysicalPathLaw_isMarkovKernel {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) :
    IsMarkovKernel (gmpPhysicalPathLaw hd ω lam Λ hΛ hω hSmooth) :=
  (gmpPhysicalPathLaw_spec hd ω lam Λ hΛ hω hSmooth).1

/-- Field `transitionKernel_isMarkovKernel` for the physical realization. -/
theorem gmpPhysicalTransitionKernel_isMarkovKernel {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) :
    ∀ t, IsMarkovKernel (gmpPhysicalTransitionKernel hd ω lam Λ hΛ hω hSmooth t) :=
  (gmpPhysicalC0KernelSemigroup_conservative hd ω lam Λ hΛ hω hSmooth).isMarkovKernel

/-- Field `transitionKernel_zero` for the physical realization. -/
theorem gmpPhysicalTransitionKernel_zero {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) :
    gmpPhysicalTransitionKernel hd ω lam Λ hΛ hω hSmooth 0 = Kernel.id :=
  (gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth).kernel_zero

/-- Field `transitionKernel_add` for the physical realization. -/
theorem gmpPhysicalTransitionKernel_add {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) :
    ∀ s t, gmpPhysicalTransitionKernel hd ω lam Λ hΛ hω hSmooth (s + t) =
      gmpPhysicalTransitionKernel hd ω lam Λ hΛ hω hSmooth t ∘ₖ
        gmpPhysicalTransitionKernel hd ω lam Λ hΛ hω hSmooth s :=
  (gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth).kernel_add

/-- Field `pathLaw_starts_at` for the physical realization. -/
theorem gmpPhysicalPathLaw_starts_at {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) :
    ∀ x, ∀ᵐ γ ∂(gmpPhysicalPathLaw hd ω lam Λ hΛ hω hSmooth x), pathPosition 0 γ = x :=
  fun x => k11_starts_at _ _ (gmpPhysicalPathLaw_spec hd ω lam Λ hΛ hω hSmooth).2 x

/-- Field `pathLaw_endpoint` for the physical realization. -/
theorem gmpPhysicalPathLaw_endpoint {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) :
    ∀ t x, ((gmpPhysicalPathLaw hd ω lam Λ hΛ hω hSmooth) x).map (pathPosition t) =
      gmpPhysicalTransitionKernel hd ω lam Λ hΛ hω hSmooth t x :=
  fun t x => k11_endpoint _ _ (gmpPhysicalPathLaw_spec hd ω lam Λ hΛ hω hSmooth).2 t x

/-- Field `pathLaw_ordered_finite_dimensional` for the physical realization. -/
theorem gmpPhysicalPathLaw_ordered_finite_dimensional {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) :
    ∀ (increments : List ℝ≥0) (x : Vec d) (F : List (Vec d) → ℝ),
      Measurable F → (∃ B : ℝ, ∀ z, |F z| ≤ B) →
        (∫ γ, F (pathPositionsAtTimes (cumulativeTimes increments) γ)
          ∂(gmpPhysicalPathLaw hd ω lam Λ hΛ hω hSmooth x)) =
          iteratedMarkovCylinderIntegral
            (gmpPhysicalTransitionKernel hd ω lam Λ hΛ hω hSmooth) increments F x := by
  intro increments x F hF ⟨B, hB⟩
  have := gmpPhysicalPathLaw_isMarkovKernel hd ω lam Λ hΛ hω hSmooth
  exact k11_fdd_general _ (gmpPhysicalC0KernelSemigroup_conservative hd ω lam Λ hΛ hω hSmooth)
    _ (gmpPhysicalPathLaw_spec hd ω lam Λ hΛ hω hSmooth).2 increments x F hF B hB

end EinsteinFull.Blueprint
