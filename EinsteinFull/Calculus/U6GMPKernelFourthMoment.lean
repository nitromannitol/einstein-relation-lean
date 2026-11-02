import EinsteinFull.Calculus.C8FoundationGMPAssociation
import EinsteinFull.Regeneration.TrajectoryShift

/-! Short-time extended fourth-moment estimate for the physical kernel. -/

open MeasureTheory ProbabilityTheory Preorder
open scoped NNReal ENNReal

noncomputable section

namespace EinsteinFull.Blueprint

open EinsteinRelation EinsteinRelation.External.GantertSection7Support

/-- The local fourth-moment estimate, in the extended nonnegative form needed
for kernel composition. The constant is strictly positive and uniform in the
starting point. -/
theorem u6_gmpPhysicalC0KernelSemigroup_fourth_moment_local
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧ ∀ (x : Vec d) (t : ℝ≥0), (t : ℝ) ≤ δ →
      (∫⁻ y, ENNReal.ofReal (euclideanNorm (y - x) ^ 4)
        ∂(gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x)) ≤
        ENNReal.ofReal (C * (t : ℝ) ^ 2) := by
  obtain ⟨C, δ, hC, hδ, hm⟩ :=
    gmpPhysicalC0KernelSemigroup_euclideanNormFourth_local_integrable_le hd ω lam Λ hΛ hω hSmooth
  refine ⟨C + 1, δ, by linarith, hδ, ?_⟩
  intro x t ht
  rw [← ofReal_integral_eq_lintegral_ofReal (hm x t ht).1
    (ae_of_all _ (fun y => by positivity))]
  apply ENNReal.ofReal_le_ofReal
  have hp : 0 ≤ (t : ℝ) ^ 2 := sq_nonneg _
  nlinarith [(hm x t ht).2]

/-- The fourth power of a finite sum of nonnegative increments has the
standard cubic dependence on the number of increments. -/
theorem u6_fourth_power_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ s, 0 ≤ f i) :
    (∑ i ∈ s, f i) ^ 4 ≤ (s.card : ℝ) ^ 3 * ∑ i ∈ s, f i ^ 4 := by
  have h := Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg s
    (f := f) (p := (4 : ℝ)) (by norm_num) hf
  norm_num only [show (4 : ℝ) - 1 = 3 by norm_num, Real.rpow_natCast] at h
  have hleft : (∑ i ∈ s, f i) ^ (4 : ℝ) = (∑ i ∈ s, f i) ^ (4 : ℕ) := by
    simpa using Real.rpow_natCast (∑ i ∈ s, f i) 4
  have hcard : (s.card : ℝ) ^ (3 : ℝ) = (s.card : ℝ) ^ (3 : ℕ) := by
    simpa using Real.rpow_natCast (s.card : ℝ) 3
  have hpoint (i : ι) : f i ^ (4 : ℝ) = f i ^ (4 : ℕ) := by
    simpa using Real.rpow_natCast (f i) 4
  rw [hleft, hcard] at h
  simp_rw [hpoint] at h
  exact h


/-- Every nonnegative time admits a positive number of equal steps, with
step size at most the prescribed scale and linear growth of the step count. -/
theorem u6_equal_time_steps (t δ : ℝ) (ht : 0 ≤ t) (hδ : 0 < δ) :
    ∃ n : ℕ, 0 < n ∧ t / (n : ℝ) ≤ δ ∧ (n : ℝ) ≤ t / δ + 1 := by
  let n := ⌊t / δ⌋₊ + 1
  have hdiv : 0 ≤ t / δ := div_nonneg ht hδ.le
  have hfloor := Nat.floor_le hdiv
  have hlt := Nat.lt_floor_add_one (t / δ)
  have hn : 0 < (n : ℝ) := by dsimp [n]; positivity
  refine ⟨n, by dsimp [n]; omega, ?_, ?_⟩
  · apply (div_le_iff₀ hn).2
    have hm : (t / δ) * δ = t := div_mul_cancel₀ t hδ.ne'
    have hbound : t / δ ≤ (n : ℝ) := by
      simpa only [n, Nat.cast_add, Nat.cast_one] using hlt.le
    nlinarith
  · dsimp [n]
    push_cast
    linarith

/-- A linear bound on the number of steps gives the required quadratic and
quartic growth after multiplying by the square of elapsed time. -/
theorem u6_step_count_growth_bound (t δ : ℝ) (n : ℕ)
    (ht : 0 ≤ t) (hδ : 0 < δ) (hn : (n : ℝ) ≤ t / δ + 1) :
    (n : ℝ) ^ 2 * t ^ 2 ≤
      (2 * (1 + δ⁻¹ ^ 2)) * (t ^ 2 + t ^ 4) := by
  have hq : 0 ≤ t / δ := div_nonneg ht hδ.le
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hsq : (n : ℝ) ^ 2 ≤ 2 * (1 + (t / δ) ^ 2) := by
    nlinarith [sq_nonneg ((t / δ) - 1), sq_nonneg ((t / δ + 1) - n)]
  calc
    (n : ℝ) ^ 2 * t ^ 2 ≤ 2 * (1 + (t / δ) ^ 2) * t ^ 2 :=
      mul_le_mul_of_nonneg_right hsq (sq_nonneg t)
    _ = 2 * (t ^ 2 + δ⁻¹ ^ 2 * t ^ 4) := by rw [div_eq_mul_inv]; ring
    _ ≤ (2 * (1 + δ⁻¹ ^ 2)) * (t ^ 2 + t ^ 4) := by
      have h1 : 0 ≤ δ⁻¹ ^ 2 * t ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
      have h2 : 0 ≤ t ^ 4 := by positivity
      nlinarith

/-- Along any finite chain, the displacement is controlled by the sum of
its increments. This applies pointwise to paths sampled from the kernels. -/
theorem u6_chain_fourth_displacement_le {d : ℕ} (p : ℕ → Vec d) (n : ℕ) :
    euclideanNorm (p n - p 0) ^ 4 ≤
      (n : ℝ) ^ 3 * ∑ i ∈ Finset.range n,
        euclideanNorm (p (i + 1) - p i) ^ 4 := by
  have hnorm (v : Vec d) : 0 ≤ euclideanNorm v := Real.sqrt_nonneg _
  have hchain : euclideanNorm (p n - p 0) ≤
      ∑ i ∈ Finset.range n, euclideanNorm (p (i + 1) - p i) := by
    induction n with
    | zero => simp [euclideanNorm, euclideanSq, dot]
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have htri := EinsteinRelation.TimeChange.euclideanNorm_add_le
        (p (n + 1) - p n) (p n - p 0)
      have heq : (p (n + 1) - p n) + (p n - p 0) = p (n + 1) - p 0 := by
        ext i; simp
      rw [heq] at htri
      linarith
  calc
    euclideanNorm (p n - p 0) ^ 4 ≤
        (∑ i ∈ Finset.range n, euclideanNorm (p (i + 1) - p i)) ^ 4 :=
      pow_le_pow_left₀ (hnorm _) hchain 4
    _ ≤ (n : ℝ) ^ 3 * ∑ i ∈ Finset.range n,
        euclideanNorm (p (i + 1) - p i) ^ 4 := by
      simpa using u6_fourth_power_sum_le (Finset.range n)
        (fun i => euclideanNorm (p (i + 1) - p i)) (by intros; exact hnorm _)

/-- Integrating the pointwise chain estimate: a uniform fourth-moment bound
for each increment yields the fourth power of the step count. -/
theorem u6_chain_fourth_moment_le {d : ℕ} {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (p : α → ℕ → Vec d) (hp : Measurable p)
    (n : ℕ) (B : ℝ≥0∞)
    (hb : ∀ i ∈ Finset.range n,
      (∫⁻ a, ENNReal.ofReal (euclideanNorm (p a (i + 1) - p a i) ^ 4) ∂μ) ≤ B) :
    (∫⁻ a, ENNReal.ofReal (euclideanNorm (p a n - p a 0) ^ 4) ∂μ) ≤
      (n : ℝ≥0∞) ^ 3 * ((n : ℝ≥0∞) * B) := by
  let f : ℕ → α → ℝ≥0∞ := fun i a =>
    ENNReal.ofReal (euclideanNorm (p a (i + 1) - p a i) ^ 4)
  have hf (i : ℕ) : Measurable (f i) := by
    dsimp [f]
    apply Measurable.ennreal_ofReal
    apply Measurable.pow_const
    apply EinsteinRelation.Entropy.continuous_euclideanNorm'.measurable.comp
    exact ((measurable_pi_apply (i + 1)).comp hp).sub ((measurable_pi_apply i).comp hp)
  calc
    _ ≤ ∫⁻ a, (n : ℝ≥0∞) ^ 3 * ∑ i ∈ Finset.range n, f i a ∂μ := by
      apply lintegral_mono
      intro a
      have h := ENNReal.ofReal_le_ofReal (u6_chain_fourth_displacement_le (p a) n)
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (n : ℝ) ^ 3),
        ENNReal.ofReal_pow (by positivity : 0 ≤ (n : ℝ)), ENNReal.ofReal_natCast,
        ENNReal.ofReal_sum_of_nonneg (s := Finset.range n)
          (f := fun i => euclideanNorm (p a (i + 1) - p a i) ^ 4)
          (fun i _ => pow_nonneg (Real.sqrt_nonneg _) 4)] at h
      exact h
    _ = (n : ℝ≥0∞) ^ 3 * ∑ i ∈ Finset.range n, ∫⁻ a, f i a ∂μ := by
      rw [lintegral_const_mul _ (Finset.measurable_sum _ fun i _ => hf i),
        lintegral_finsetSum _ (fun i _ => hf i)]
    _ ≤ (n : ℝ≥0∞) ^ 3 * ((n : ℝ≥0∞) * B) := by
      gcongr
      calc
        (∑ i ∈ Finset.range n, ∫⁻ a, f i a ∂μ) ≤ ∑ _i ∈ Finset.range n, B :=
          Finset.sum_le_sum (fun i hi => hb i hi)
        _ = (n : ℝ≥0∞) * B := by simp

/-- Each transition of the actual physical semigroup is a Markov kernel. -/
theorem u6_physical_isMarkovKernel {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω)
    (t : ℝ≥0) : IsMarkovKernel (gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t) := by
  constructor
  intro x
  exact ⟨gmpPhysicalC0KernelSemigroup_conservative hd ω lam Λ hΛ hω hSmooth t x⟩

/-- Consecutive coordinates of the seeded trajectory have the joint law of
its current marginal and one actual kernel transition. -/
theorem u6_seededTrajectory_pair {S : Type*} [MeasurableSpace S]
    (κ : Kernel S S) [IsMarkovKernel κ] (x : S) (n : ℕ) :
    (EinsteinFull.Regeneration.seededTrajectory κ Kernel.id x).map
        (fun s => (s n, s (n + 1))) =
      ((EinsteinFull.Regeneration.seededTrajectory κ Kernel.id x).map (fun s => s n)).compProd κ := by
  let μ := EinsteinFull.Regeneration.seededTrajectory κ Kernel.id x
  let f : ((j : Finset.Iic n) → S) → S := fun u => u ⟨n, Finset.mem_Iic.mpr le_rfl⟩
  have h := EinsteinFull.Regeneration.map_pair_of_prefix_transition μ (frestrictLe n)
    f (fun s => s (n + 1)) (measurable_frestrictLe n) (measurable_pi_apply _)
    (measurable_pi_apply _) (EinsteinFull.Regeneration.homogeneousHistoryKernel κ n) κ
    (EinsteinFull.Regeneration.seededTrajectory_prefix_next_joint κ Kernel.id x n)
    (Filter.Eventually.of_forall (fun _ => rfl))
  exact h

/-- A uniform kernel increment estimate holds at every step of the seeded
trajectory, including after averaging over the random current state. -/
theorem u6_seededTrajectory_increment_bound {d : ℕ}
    (κ : Kernel (Vec d) (Vec d)) [IsMarkovKernel κ] (x : Vec d)
    (B : ℝ≥0∞) (hB : ∀ z, (∫⁻ y,
      ENNReal.ofReal (euclideanNorm (y - z) ^ 4) ∂κ z) ≤ B) (n : ℕ) :
    (∫⁻ s, ENNReal.ofReal (euclideanNorm (s (n + 1) - s n) ^ 4)
      ∂(EinsteinFull.Regeneration.seededTrajectory κ Kernel.id x)) ≤ B := by
  let μ := EinsteinFull.Regeneration.seededTrajectory κ Kernel.id x
  let g : Vec d × Vec d → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (euclideanNorm (z.2 - z.1) ^ 4)
  have hg : Measurable g := by
    dsimp [g]
    apply Measurable.ennreal_ofReal
    apply Measurable.pow_const
    exact EinsteinRelation.Entropy.continuous_euclideanNorm'.measurable.comp
      (measurable_snd.sub measurable_fst)
  have hm : Measurable (fun s : ℕ → Vec d => (s n, s (n + 1))) := by fun_prop
  calc
    _ = ∫⁻ z, g z ∂(μ.map (fun s => (s n, s (n + 1)))) :=
      (lintegral_map hg hm).symm
    _ = ∫⁻ z, g z ∂((μ.map (fun s => s n)).compProd κ) := by
      rw [u6_seededTrajectory_pair]
    _ = ∫⁻ z, ∫⁻ y, g (z, y) ∂κ z ∂(μ.map (fun s => s n)) :=
      Measure.lintegral_compProd hg
    _ ≤ ∫⁻ _z, B ∂(μ.map (fun s => s n)) := lintegral_mono hB
    _ = B := by
      rw [lintegral_const, Measure.map_apply (measurable_pi_apply n) MeasurableSet.univ]
      simp

/-- The coordinate at step n of the trajectory has the semigroup law at
elapsed time n times the step size. -/
theorem u6_seededTrajectory_endpoint {S : Type*} [MeasurableSpace S]
    (P : MarkovProcess.SubMarkovKernelSemigroup S) (t : ℝ≥0)
    [IsMarkovKernel (P t)] (x : S) (n : ℕ) :
    (EinsteinFull.Regeneration.seededTrajectory (P t) Kernel.id x).map (fun s => s n) =
      P (n • t) x := by
  let μ := EinsteinFull.Regeneration.seededTrajectory (P t) Kernel.id x
  induction n with
  | zero =>
    have h := congrArg (fun κ : Kernel S S => κ x)
      (EinsteinFull.Regeneration.map_seededTrajectory_zero (P t) Kernel.id)
    rw [Kernel.map_apply _ (measurable_pi_apply 0)] at h
    simpa [P.kernel_zero] using h
  | succ n ih =>
    calc
      μ.map (fun s => s (n + 1)) =
          (μ.map (fun s => (s n, s (n + 1)))).snd := by
        rw [Measure.snd, Measure.map_map measurable_snd (by fun_prop)]
        rfl
      _ = ((μ.map (fun s => s n)).compProd (P t)).snd := by
        rw [u6_seededTrajectory_pair]
      _ = (P t) ∘ₘ (μ.map (fun s => s n)) := Measure.snd_compProd _ _
      _ = ((P t).comp (P (n • t))) x := by rw [ih, Kernel.comp_apply]
      _ = P ((n + 1) • t) x := by
        rw [add_nsmul, one_nsmul, P.kernel_add]

/-- A uniform one-step estimate propagates through the actual semigroup,
with the fourth-power dependence on the number of equal steps. -/
theorem u6_semigroup_fourth_moment_steps {d : ℕ}
    (P : MarkovProcess.SubMarkovKernelSemigroup (Vec d)) (t : ℝ≥0)
    [IsMarkovKernel (P t)] (x : Vec d) (n : ℕ) (B : ℝ≥0∞)
    (hB : ∀ z, (∫⁻ y, ENNReal.ofReal (euclideanNorm (y - z) ^ 4) ∂P t z) ≤ B) :
    (∫⁻ y, ENNReal.ofReal (euclideanNorm (y - x) ^ 4) ∂P (n • t) x) ≤
      (n : ℝ≥0∞) ^ 3 * ((n : ℝ≥0∞) * B) := by
  let μ := EinsteinFull.Regeneration.seededTrajectory (P t) Kernel.id x
  have hzero : μ.map (fun s => s 0) = Measure.dirac x := by
    have h := congrArg (fun κ : Kernel (Vec d) (Vec d) => κ x)
      (EinsteinFull.Regeneration.map_seededTrajectory_zero (P t) Kernel.id)
    rw [Kernel.map_apply _ (measurable_pi_apply 0)] at h
    simpa [Kernel.id_apply] using h
  have ha : ∀ᵐ s ∂μ, s 0 = x := by
    apply (ae_map_iff (p := fun y : Vec d => y = x)
      (show Measurable (fun s : ℕ → Vec d => s 0) from measurable_pi_apply 0).aemeasurable
      (show MeasurableSet {y : Vec d | y = x} from measurableSet_singleton x)).1
    rw [hzero]
    simp
  have hf : Measurable (fun y : Vec d => ENNReal.ofReal (euclideanNorm (y - x) ^ 4)) := by
    apply Measurable.ennreal_ofReal
    apply Measurable.pow_const
    exact EinsteinRelation.Entropy.continuous_euclideanNorm'.measurable.comp
      (measurable_id.sub measurable_const)
  calc
    _ = ∫⁻ s, ENNReal.ofReal (euclideanNorm (s n - x) ^ 4) ∂μ := by
      rw [← u6_seededTrajectory_endpoint P t x n, lintegral_map hf (measurable_pi_apply n)]
    _ = ∫⁻ s, ENNReal.ofReal (euclideanNorm (s n - s 0) ^ 4) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ha] with s hs
      rw [hs]
    _ ≤ _ := u6_chain_fourth_moment_le μ id measurable_id n B
      (fun i _ => u6_seededTrajectory_increment_bound (P t) x B hB i)


/-- The physical kernel has a uniform fourth-moment bound at every time. -/
theorem u6_gmpPhysicalC0KernelSemigroup_fourth_moment
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0) (x : Vec d),
      (∫⁻ y, ENNReal.ofReal (euclideanNorm (y - x) ^ 4)
        ∂(gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x)) ≤
        ENNReal.ofReal C * (((t : ℝ≥0∞) ^ 2) + ((t : ℝ≥0∞) ^ 4)) := by
  obtain ⟨C, δ, hC, hδ, hm⟩ :=
    u6_gmpPhysicalC0KernelSemigroup_fourth_moment_local hd ω lam Λ hΛ hω hSmooth
  refine ⟨C * (2 * (1 + δ⁻¹ ^ 2)), by positivity, ?_⟩
  intro t x
  obtain ⟨n, hn, hstep, hcount⟩ := u6_equal_time_steps (t : ℝ) δ t.property hδ
  let u : ℝ≥0 := t / (n : ℝ≥0)
  have hnNN : (n : ℝ≥0) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hnReal : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hu : (u : ℝ) = (t : ℝ) / (n : ℝ) := by simp [u]
  have ht : n • u = t := by
    rw [nsmul_eq_mul]
    change (n : ℝ≥0) * (t / (n : ℝ≥0)) = t
    rw [mul_comm, div_mul_cancel₀ _ hnNN]
  let P := gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth
  letI : IsMarkovKernel (P u) := u6_physical_isMarkovKernel hd ω lam Λ hΛ hω hSmooth u
  have hlocal : ∀ z, (∫⁻ y, ENNReal.ofReal (euclideanNorm (y - z) ^ 4) ∂P u z) ≤
      ENNReal.ofReal (C * (u : ℝ) ^ 2) := by
    intro z
    exact hm z u (by simpa [hu] using hstep)
  have hsem := u6_semigroup_fourth_moment_steps P u x n
    (ENNReal.ofReal (C * (u : ℝ) ^ 2)) hlocal
  rw [ht] at hsem
  have hprod : (n : ℝ) ^ 3 * ((n : ℝ) * (C * (u : ℝ) ^ 2)) =
      C * ((n : ℝ) ^ 2 * (t : ℝ) ^ 2) := by
    rw [hu]
    field_simp
    <;> ring
  have hcast : (n : ℝ≥0∞) ^ 3 * ((n : ℝ≥0∞) * ENNReal.ofReal (C * (u : ℝ) ^ 2)) =
      ENNReal.ofReal (C * ((n : ℝ) ^ 2 * (t : ℝ) ^ 2)) := by
    rw [← hprod, ENNReal.ofReal_mul (by positivity : 0 ≤ (n : ℝ) ^ 3),
      ENNReal.ofReal_mul hn0, ENNReal.ofReal_pow hn0, ENNReal.ofReal_natCast]
  have hb := mul_le_mul_of_nonneg_left
    (u6_step_count_growth_bound (t : ℝ) δ n t.property hδ hcount) hC.le
  have htcast : ENNReal.ofReal ((C * (2 * (1 + δ⁻¹ ^ 2))) *
      ((t : ℝ) ^ 2 + (t : ℝ) ^ 4)) =
      ENNReal.ofReal (C * (2 * (1 + δ⁻¹ ^ 2))) *
        (((t : ℝ≥0∞) ^ 2) + ((t : ℝ≥0∞) ^ 4)) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add (sq_nonneg _) (by positivity),
      ENNReal.ofReal_pow (show 0 ≤ (t : ℝ) from t.property) 2,
      ENNReal.ofReal_pow (show 0 ≤ (t : ℝ) from t.property) 4,
      ENNReal.ofReal_coe_nnreal]
  calc
    _ ≤ (n : ℝ≥0∞) ^ 3 * ((n : ℝ≥0∞) * ENNReal.ofReal (C * (u : ℝ) ^ 2)) := hsem
    _ = ENNReal.ofReal (C * ((n : ℝ) ^ 2 * (t : ℝ) ^ 2)) := hcast
    _ ≤ ENNReal.ofReal ((C * (2 * (1 + δ⁻¹ ^ 2))) *
        ((t : ℝ) ^ 2 + (t : ℝ) ^ 4)) := ENNReal.ofReal_le_ofReal (by nlinarith [hb])
    _ = _ := htcast

end EinsteinFull.Blueprint

#print axioms EinsteinFull.Blueprint.u6_gmpPhysicalC0KernelSemigroup_fourth_moment_local
#print axioms EinsteinFull.Blueprint.u6_fourth_power_sum_le

#print axioms EinsteinFull.Blueprint.u6_equal_time_steps

#print axioms EinsteinFull.Blueprint.u6_step_count_growth_bound

#print axioms EinsteinFull.Blueprint.u6_chain_fourth_displacement_le

#print axioms EinsteinFull.Blueprint.u6_chain_fourth_moment_le

#print axioms EinsteinFull.Blueprint.u6_physical_isMarkovKernel
#print axioms EinsteinFull.Blueprint.u6_seededTrajectory_pair

#print axioms EinsteinFull.Blueprint.u6_seededTrajectory_increment_bound

#print axioms EinsteinFull.Blueprint.u6_seededTrajectory_endpoint

#print axioms EinsteinFull.Blueprint.u6_semigroup_fourth_moment_steps

#print axioms EinsteinFull.Blueprint.u6_gmpPhysicalC0KernelSemigroup_fourth_moment
