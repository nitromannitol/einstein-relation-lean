import EinsteinFull.Calculus.CLUnforcedClockShift
import EinsteinFull.Calculus.C20UnforcedClockRate

/-!
# L² law of large numbers for the unforced clock

On smooth environments the centered clock of the supplied unforced reduced law has vanishing
normalized L² error under the annealed law. The Markov property and stationarity reduce the
two-time correlations to the semigroup pairing `⟨f, P_r f⟩` of the centered clock observation,
whose time averages vanish by mean ergodicity.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace EinsteinFull.Blueprint
open EinsteinFull EinsteinRelation

variable {d : ℕ}

/-- The centered clock density at the origin, clamped to the bounds of a regular environment. -/
noncomputable def clampedClock (Λ m : ℝ) (ω : FieldPair d) : ℝ :=
  max (min (clockDensity ω 0) (Real.exp (2 * Λ))) (Real.exp (-2 * Λ)) - m

theorem continuous_clampedClock (Λ m : ℝ) : Continuous (clampedClock (d := d) Λ m) :=
  ((((Real.continuous_exp.comp (continuous_const.mul
    ((continuous_eval_const 0).comp continuous_snd))).min continuous_const).max
      continuous_const).sub continuous_const)

theorem abs_clampedClock_le (Λ m : ℝ) (ω : FieldPair d) :
    |clampedClock Λ m ω| ≤ Real.exp (2 * Λ) + Real.exp (-2 * Λ) + |m| := by
  unfold clampedClock
  have h1 : 0 ≤ max (min (clockDensity ω 0) (Real.exp (2 * Λ))) (Real.exp (-2 * Λ)) :=
    (Real.exp_pos _).le.trans (le_max_right _ _)
  have h2 : max (min (clockDensity ω 0) (Real.exp (2 * Λ))) (Real.exp (-2 * Λ)) ≤
      Real.exp (2 * Λ) + Real.exp (-2 * Λ) :=
    max_le ((min_le_right _ _).trans (le_add_of_nonneg_right (Real.exp_pos _).le))
      (le_add_of_nonneg_left (Real.exp_pos _).le)
  calc _ ≤ |max (min (clockDensity ω 0) (Real.exp (2 * Λ))) (Real.exp (-2 * Λ))| + |m| :=
        abs_sub _ _
    _ ≤ _ := by rw [abs_of_nonneg h1]; linarith

/-- On a regular environment the clamped clock of every translate is the centered density. -/
theorem clampedClock_translate {Λ : ℝ} (m : ℝ) {ω : FieldPair d} (hω : IsRegular Λ ω)
    (x : Vec d) : clampedClock Λ m (translate x ω) = clockDensity ω x - m := by
  have hb := clockDensity_bounds ω x Λ (hω.2.1 x)
  have e : clockDensity (translate x ω) 0 = clockDensity ω x := by
    simp [clockDensity, translate_scalar]
  unfold clampedClock
  rw [e, min_eq_left hb.2, max_eq_left hb.1]

/-- On a regular environment the centered clock is the time integral of the clamped clock of the
environment seen from the particle. -/
theorem physicalPathClock_sub_eq_integral {Λ : ℝ} (m : ℝ) {ω : FieldPair d} (hω : IsRegular Λ ω)
    (γ : Path d) (T : ℝ≥0) :
    (Clock.physicalPathClock ω γ T : ℝ) - T * m =
      ∫ u in (0 : ℝ)..(T : ℝ), clampedClock Λ m (translate (γ u.toNNReal) ω) := by
  have hc : Continuous fun u : ℝ => clockDensity ω (γ u.toNNReal) :=
    (Real.continuous_exp.comp (continuous_const.mul ω.2.continuous)).comp
      (γ.continuous.comp continuous_real_toNNReal)
  simp_rw [clampedClock_translate m hω]
  rw [intervalIntegral.integral_sub (hc.intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_const, smul_eq_mul, sub_zero, Clock.coe_physicalPathClock]
  rfl

/-- The clamped clock of the environment seen from the particle is jointly continuous in time
and in the environment–path pair. -/
theorem continuous_clampedClock_path (Λ m : ℝ) :
    Continuous fun p : ℝ × (FieldPair d × Path d) =>
      clampedClock Λ m (translate (p.2.2 p.1.toNNReal) p.2.1) :=
  (continuous_clampedClock Λ m).comp (Probability.continuous_translate.comp
    ((continuous_snd.comp continuous_snd).eval (continuous_real_toNNReal.comp continuous_fst)
      |>.prodMk (continuous_fst.comp continuous_snd)))

/-- Markov two-time identity for the clamped clock along textbook reduced paths started at the
origin of a regular environment. -/
theorem integral_clampedClock_mul_of_le (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 0 < Λ) (m : ℝ)
    {K : Kernel (FieldPair d × Vec d) (Path d)} [IsMarkovKernel K]
    (hK : ∀ ω : FieldPair d, IsRegular Λ ω → ∀ x : Vec d,
      SolvesMartingaleProblem (External.Draft.svGenerator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) (⟨0, by omega⟩ : Fin d) 0)) x (K (ω, x)))
    {ω : FieldPair d} (hω : IsRegular Λ ω) {u v : ℝ≥0} (huv : u ≤ v) :
    ∫ γ, clampedClock Λ m (translate (γ u) ω) * clampedClock Λ m (translate (γ v) ω) ∂K (ω, 0) =
      ∫ γ, clampedClock Λ m (translate (γ u) ω) *
        ∫ η, clampedClock Λ m (translate (η (v - u)) (translate (γ u) ω))
          ∂K (translate (γ u) ω, 0) ∂K (ω, 0) := by
  let i : Fin d := ⟨0, by omega⟩
  obtain ⟨M, hM⟩ := reduced_bddCoef hΛ i 0 hω
  have hcc := continuous_clampedClock (d := d) Λ m
  have htr : Continuous fun x : Vec d => translate x ω :=
    Probability.continuous_translate.comp (continuous_id.prodMk continuous_const)
  let G : Path d → ℝ := fun η => clampedClock Λ m (translate (η (v - u)) ω)
  have hG : Measurable G :=
    (hcc.comp (htr.comp (continuous_eval_const (v - u)))).measurable
  have hpos : Measurable[pathFiltration d u] (pathPosition (d := d) u) :=
    (Filtration.stronglyAdapted_natural
      (fun t => (measurable_pathPosition t).stronglyMeasurable) u).measurable
  have hH : StronglyMeasurable[pathFiltration d u]
      (fun γ : Path d => clampedClock Λ m (translate (γ u) ω)) :=
    ((hcc.comp htr).measurable.comp hpos).stronglyMeasurable
  have hmk := integral_mul_restartPath hM (hK ω hω 0) (fun y => K (ω, y))
    (fun y P' hP' => reducedKernel_eq_of_solves hΛ i 0 hK (by omega) hω y hP') u hH
    (fun γ => abs_clampedClock_le Λ m _) hG (fun η => abs_clampedClock_le Λ m _)
  have hrestart (γ : Path d) :
      G (restartPath u γ) = clampedClock Λ m (translate (γ v) ω) := by
    change clampedClock Λ m (translate (γ (u + (v - u))) ω) = _
    rw [add_tsub_cancel_of_le huv]
  have hcond (y : Vec d) : (∫ η, G η ∂K (ω, y)) =
      ∫ η, clampedClock Λ m (translate (η (v - u)) (translate y ω)) ∂K (translate y ω, 0) := by
    rw [reducedKernel_translate hΛ i 0 hK (by omega) hω y,
      integral_map (measurable_translatePath y).aemeasurable hG.aestronglyMeasurable]
    refine integral_congr_ae (ae_of_all _ fun η => ?_)
    change clampedClock Λ m (translate (y + η (v - u)) ω) =
      clampedClock Λ m (translate (η (v - u)) (translate y ω))
    rw [translate_add, add_comm]
  simp only [hrestart] at hmk
  rw [hmk]
  simp_rw [hcond]

/-- The clamped clock observed along the textbook reduced kernel at time `r`. -/
noncomputable def kernelClockMean (Λ m : ℝ) (K : Kernel (FieldPair d × Vec d) (Path d))
    (r : ℝ≥0) (ω : FieldPair d) : ℝ :=
  ∫ η, clampedClock Λ m (translate (η r) ω) ∂K (ω, 0)

theorem measurable_kernelClockMean (Λ m : ℝ) (K : Kernel (FieldPair d × Vec d) (Path d))
    [IsMarkovKernel K] (r : ℝ≥0) : Measurable (kernelClockMean Λ m K r) := by
  let K0 : Kernel (FieldPair d) (Path d) :=
    K.comap (fun ω => (ω, (0 : Vec d))) (measurable_id.prodMk measurable_const)
  have hf : StronglyMeasurable (Function.uncurry fun (ω : FieldPair d) (η : Path d) =>
      clampedClock Λ m (translate (η r) ω)) :=
    ((continuous_clampedClock Λ m).comp (Probability.continuous_translate.comp
      ((continuous_snd.eval continuous_const).prodMk continuous_fst))).stronglyMeasurable
  exact (StronglyMeasurable.integral_kernel_prod_right (κ := K0) hf).measurable

theorem abs_kernelClockMean_le (Λ m : ℝ) (K : Kernel (FieldPair d × Vec d) (Path d))
    [IsMarkovKernel K] (r : ℝ≥0) (ω : FieldPair d) :
    |kernelClockMean Λ m K r ω| ≤ Real.exp (2 * Λ) + Real.exp (-2 * Λ) + |m| := by
  have h := norm_integral_le_of_norm_le_const (μ := K (ω, 0))
    (C := Real.exp (2 * Λ) + Real.exp (-2 * Λ) + |m|)
    (f := fun η => clampedClock Λ m (translate (η r) ω)) (ae_of_all _ fun η => by
      simpa only [Real.norm_eq_abs] using abs_clampedClock_le Λ m _)
  have h1 : (K (ω, 0)).real Set.univ = 1 := by simp [Measure.real]
  simpa only [kernelClockMean, Real.norm_eq_abs, h1, mul_one] using h



/-- The square of an interval integral is the double integral of the product. -/
theorem sq_intervalIntegral_eq (g : ℝ → ℝ) (a b : ℝ) :
    (∫ u in a..b, g u) ^ 2 = ∫ u in a..b, ∫ v in a..b, g u * g v := by
  rw [sq, ← intervalIntegral.integral_mul_const]
  refine intervalIntegral.integral_congr fun u _ => ?_
  rw [intervalIntegral.integral_const_mul]

/-- A bounded jointly measurable integrand can be integrated first in time. -/
theorem integral_intervalIntegral_comm {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsFiniteMeasure μ] {F : ℝ → Ω → ℝ} (hF : Measurable (Function.uncurry F)) {C : ℝ}
    (hC : ∀ u z, |F u z| ≤ C) {a b : ℝ} (hab : a ≤ b) :
    ∫ z, (∫ u in a..b, F u z) ∂μ = ∫ u in a..b, ∫ z, F u z ∂μ := by
  simp_rw [intervalIntegral.integral_of_le hab]
  have hint : Integrable (Function.uncurry fun z u => F u z)
      (μ.prod (volume.restrict (Set.Ioc a b))) :=
    Integrable.of_bound (hF.comp measurable_swap).aestronglyMeasurable C
      (ae_of_all _ fun p => by rw [Real.norm_eq_abs]; exact hC p.2 p.1)
  exact integral_integral_swap hint

/-- The interval integral of a bounded jointly measurable family is jointly measurable and
bounded. -/
theorem measurable_intervalIntegral_param {Ω : Type*} [MeasurableSpace Ω]
    {F : ℝ → ℝ → Ω → ℝ} (hF : Measurable fun p : ℝ × ℝ × Ω => F p.1 p.2.1 p.2.2)
    {a b : ℝ} (hab : a ≤ b) :
    Measurable fun p : ℝ × Ω => ∫ v in a..b, F p.1 v p.2 := by
  simp_rw [intervalIntegral.integral_of_le hab]
  have h : StronglyMeasurable fun q : (ℝ × Ω) × ℝ => F q.1.1 q.2 q.1.2 :=
    (hF.comp ((measurable_fst.comp measurable_fst).prodMk
      (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))).stronglyMeasurable
  exact (h.integral_prod_right' (ν := volume.restrict (Set.Ioc a b))).measurable


/-- A continuous linear image of an orbit at the distances to `u ∈ [0, T]` integrates over
`[0, T]` to the images of two orbit averages. -/
theorem norm_intervalIntegral_dist_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {g : ℝ → E} (hg : Continuous g) (ℓ : E →L[ℂ] ℂ) {u T : ℝ}
    (hu : 0 ≤ u) (huT : u ≤ T) :
    ‖∫ v in (0 : ℝ)..T, ℓ (g |v - u|)‖ ≤
      ‖ℓ‖ * (‖∫ r in (0 : ℝ)..u, g r‖ + ‖∫ r in (0 : ℝ)..(T - u), g r‖) := by
  have hc : Continuous fun v : ℝ => ℓ (g |v - u|) :=
    ℓ.continuous.comp (hg.comp (continuous_id.sub continuous_const).abs)
  have hgi (a b : ℝ) : IntervalIntegrable g volume a b := hg.intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 u)
    (hc.intervalIntegrable u T)]
  have h1 : (∫ v in (0 : ℝ)..u, ℓ (g |v - u|)) = ℓ (∫ r in (0 : ℝ)..u, g r) := by
    have e : (∫ v in (0 : ℝ)..u, ℓ (g |v - u|)) = ∫ v in (0 : ℝ)..u, ℓ (g (u - v)) := by
      refine intervalIntegral.integral_congr fun v hv => ?_
      rw [Set.uIcc_of_le hu] at hv
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hv.2)]
    rw [e, intervalIntegral.integral_comp_sub_left (fun r => ℓ (g r)) u, sub_self, sub_zero,
      ℓ.intervalIntegral_comp_comm (hgi 0 u)]
  have h2 : (∫ v in u..T, ℓ (g |v - u|)) = ℓ (∫ r in (0 : ℝ)..(T - u), g r) := by
    have e : (∫ v in u..T, ℓ (g |v - u|)) = ∫ v in u..T, ℓ (g (v - u)) := by
      refine intervalIntegral.integral_congr fun v hv => ?_
      rw [Set.uIcc_of_le huT] at hv
      rw [abs_of_nonneg (sub_nonneg.2 hv.1)]
    rw [e, intervalIntegral.integral_comp_sub_right (fun r => ℓ (g r)) u, sub_self,
      ℓ.intervalIntegral_comp_comm (hgi 0 (T - u))]
  rw [h1, h2, mul_add]
  exact (norm_add_le _ _).trans (add_le_add (ℓ.le_opNorm _) (ℓ.le_opNorm _))


section Annealed

variable (hd : 2 ≤ d) (D : StructuralData d)
  (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
  (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q)
  {K : Kernel (FieldPair d × Vec d) (Path d)} [IsMarkovKernel K]
  (hK : ∀ ω : FieldPair d, IsRegular D.ellipticity ω → ∀ x : Vec d,
    SolvesMartingaleProblem (External.Draft.svGenerator (reducedCoefficient ω)
      (forcedDrift (reducedCoefficient ω) (⟨0, by omega⟩ : Fin d) 0)) x (K (ω, x)))

include hQ hunforced hpath hK in
/-- Under the textbook reduced kernel the reduced and the physical environments seen from the
particle have the reduced and the environment law at every time. -/
theorem map_translate_reducedKernel (t : ℝ≥0) :
    Measure.map (fun z : FieldPair d × Path d => translate (z.2 t) (reduce z.1))
        (Q.measure ⊗ₘ K.comap (fun ω => (ω, (0 : Vec d))) (measurable_id.prodMk measurable_const)) =
      reducedLaw Q ∧
    Measure.map (fun z : FieldPair d × Path d => translate (z.2 t) z.1)
        (Q.measure ⊗ₘ K.comap (fun ω => (ω, (0 : Vec d))) (measurable_id.prodMk measurable_const)) =
      Q.measure := by
  have hK0 : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
      (reducedGenerator (⟨0, by omega⟩ : Fin d) ω 0) 0
      (K.comap (fun ω => (ω, (0 : Vec d))) (measurable_id.prodMk measurable_const) ω) := by
    filter_upwards [Q.regular, hQ] with ω hω hsm
    exact (reducedGenerator_solves_iff hsm.1 _ 0 0 _).2 (hK ω hω 0)
  have hred := u3_unforced_annealed_marginal_of_deps (hunforced := hunforced) (hpath := hpath)
    hd Q _ hK0 t
  exact ⟨hred, map_translate_eq_of_reduced Q _ t hred⟩

include hQ hunforced hpath hK in
/-- Annealed two-time correlation of the clamped clock. -/
theorem annealed_clampedClock_mul_of_le (m : ℝ) {u v : ℝ≥0} (huv : u ≤ v) :
    ∫ z, clampedClock D.ellipticity m (translate (z.2 u) z.1) *
        clampedClock D.ellipticity m (translate (z.2 v) z.1)
        ∂(Q.measure ⊗ₘ K.comap (fun ω => (ω, (0 : Vec d)))
          (measurable_id.prodMk measurable_const)) =
      ∫ ω, clampedClock D.ellipticity m ω * kernelClockMean D.ellipticity m K (v - u) ω
        ∂Q.measure := by
  have : IsProbabilityMeasure Q.measure := Q.probability
  let K0 : Kernel (FieldPair d) (Path d) :=
    K.comap (fun ω => (ω, (0 : Vec d))) (measurable_id.prodMk measurable_const)
  have hΛ : 0 < D.ellipticity := zero_lt_one.trans_le D.one_le_ellipticity
  let B := Real.exp (2 * D.ellipticity) + Real.exp (-2 * D.ellipticity) + |m|
  have hcc := continuous_clampedClock (d := d) D.ellipticity m
  have hEt (t : ℝ≥0) : Continuous fun z : FieldPair d × Path d => translate (z.2 t) z.1 :=
    Probability.continuous_translate.comp ((continuous_snd.eval continuous_const).prodMk
      continuous_fst)
  have hint (F : FieldPair d × Path d → ℝ) (hF : Measurable F) (C : ℝ)
      (hFb : ∀ z, |F z| ≤ C) : Integrable F (Q.measure ⊗ₘ K0) :=
    Integrable.of_bound hF.aestronglyMeasurable C
      (ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using hFb z)
  have hkm := measurable_kernelClockMean D.ellipticity m K (v - u)
  have hbb (a b : ℝ) (ha : |a| ≤ B) (hb : |b| ≤ B) : |a * b| ≤ B * B := by
    rw [abs_mul]
    exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)
  let F : FieldPair d → ℝ := fun ω =>
    clampedClock D.ellipticity m ω * kernelClockMean D.ellipticity m K (v - u) ω
  have hF : Measurable F := hcc.measurable.mul hkm
  have hmarg := (map_translate_reducedKernel hd D Q hQ hunforced hpath hK u).2
  calc
    _ = ∫ ω, ∫ γ, clampedClock D.ellipticity m (translate (γ u) ω) *
          clampedClock D.ellipticity m (translate (γ v) ω) ∂K0 ω ∂Q.measure :=
      Measure.integral_compProd (hint (fun z => clampedClock D.ellipticity m
          (translate (z.2 u) z.1) * clampedClock D.ellipticity m (translate (z.2 v) z.1))
        ((hcc.comp (hEt u)).mul (hcc.comp (hEt v))).measurable (B * B) fun z =>
          hbb _ _ (abs_clampedClock_le _ m _) (abs_clampedClock_le _ m _))
    _ = ∫ ω, ∫ γ, F (translate (γ u) ω) ∂K0 ω ∂Q.measure := by
      refine integral_congr_ae (Q.regular.mono fun ω hω => ?_)
      exact integral_clampedClock_mul_of_le hd hΛ m hK hω huv
    _ = ∫ z, F (translate (z.2 u) z.1) ∂(Q.measure ⊗ₘ K0) :=
      (Measure.integral_compProd (hint (fun z => F (translate (z.2 u) z.1))
        (hF.comp (hEt u).measurable) (B * B) fun z =>
          hbb _ _ (abs_clampedClock_le _ m _) (abs_kernelClockMean_le _ m K _ _))).symm
    _ = ∫ ω, F ω ∂(Measure.map (fun z : FieldPair d × Path d => translate (z.2 u) z.1)
          (Q.measure ⊗ₘ K0)) :=
      (integral_map (hEt u).measurable.aemeasurable hF.aestronglyMeasurable).symm
    _ = _ := by rw [hmarg]

include hQ hunforced hpath hK in
/-- The annealed two-time correlation of the clamped clock is the semigroup pairing of the
centered clock observation. -/
theorem integral_clampedClock_mul_kernelClockMean (m : ℝ)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hrealize : ∀ Y : QuenchedPathLaws d,
      (∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
        (reducedGenerator (⟨0, by omega⟩ : Fin d) ω 0) 0 (Y (0, ω))) →
      ∀ (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)), ∀ᵐ ω ∂Q.measure,
        Integrable (fun γ : Path d => f (translate (γ t) (reduce ω))) (Y (0, ω)) ∧
        P t f (reduce ω) = ∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂Y (0, ω))
    (f : Lp ℂ 2 (reducedLaw Q))
    (hf : f =ᵐ[reducedLaw Q] fun ρ => ((max (min (ρ.2 0) (Real.exp (2 * D.ellipticity)))
      (Real.exp (-2 * D.ellipticity)) - m : ℝ) : ℂ))
    (r : ℝ≥0) :
    ∫ ω, clampedClock D.ellipticity m ω * kernelClockMean D.ellipticity m K r ω ∂Q.measure =
      (∫ ρ, f ρ * P r f ρ ∂reducedLaw Q).re := by
  have : IsProbabilityMeasure Q.measure := Q.probability
  let fr : FieldPair d → ℝ := fun ρ => max (min (ρ.2 0) (Real.exp (2 * D.ellipticity)))
    (Real.exp (-2 * D.ellipticity)) - m
  have hfr : Continuous fr :=
    ((((continuous_eval_const 0).comp continuous_snd).min continuous_const).max
      continuous_const).sub continuous_const
  let K0 : Kernel (FieldPair d) (Path d) :=
    K.comap (fun ω => (ω, (0 : Vec d))) (measurable_id.prodMk measurable_const)
  let Kq : QuenchedPathLaws d :=
    K.comap (fun p : Vec d × FieldPair d => (p.2, p.1)) measurable_swap
  have hKq : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
      (reducedGenerator (⟨0, by omega⟩ : Fin d) ω 0) 0 (Kq (0, ω)) := by
    filter_upwards [Q.regular, hQ] with ω hω hsm
    exact (reducedGenerator_solves_iff hsm.1 _ 0 0 _).2 (hK ω hω 0)
  have hreal := hrealize Kq hKq r f
  have hred := (map_translate_reducedKernel hd D Q hQ hunforced hpath hK r).1
  have hEr : Measurable fun z : FieldPair d × Path d => translate (z.2 r) (reduce z.1) :=
    (Probability.continuous_translate.comp ((continuous_snd.eval continuous_const).prodMk
      (Probability.continuous_reduce.comp continuous_fst))).measurable
  have hrep : ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂K0 ω,
      f (translate (γ r) (reduce ω)) = (fr (translate (γ r) (reduce ω)) : ℂ) := by
    have h1 : ∀ᵐ z ∂(Q.measure ⊗ₘ K0), f (translate (z.2 r) (reduce z.1)) =
        (fr (translate (z.2 r) (reduce z.1)) : ℂ) := by
      have hf' : ∀ᵐ ρ ∂Measure.map (fun z : FieldPair d × Path d =>
          translate (z.2 r) (reduce z.1)) (Q.measure ⊗ₘ K0), f ρ = (fr ρ : ℂ) := by
        rw [hred]
        exact hf
      exact ae_of_ae_map hEr.aemeasurable hf'
    exact Measure.ae_ae_of_ae_compProd h1
  have hkm : ∀ᵐ ω ∂Q.measure,
      kernelClockMean D.ellipticity m K r ω = (P r f (reduce ω)).re := by
    filter_upwards [hreal, hrep] with ω hω hrω
    have hrω' : ∀ᵐ γ ∂Kq (0, ω),
        f (translate (γ r) (reduce ω)) = (fr (translate (γ r) (reduce ω)) : ℂ) := hrω
    rw [hω.2]
    have hre := integral_re (𝕜 := ℂ) hω.1
    simp only [RCLike.re_to_complex] at hre
    rw [← hre]
    refine integral_congr_ae ?_
    filter_upwards [hrω'] with γ hγ
    rw [hγ, Complex.ofReal_re]
    rfl
  have hPf : Measurable fun ρ : FieldPair d => (P r f ρ).re :=
    Complex.measurable_re.comp (Lp.stronglyMeasurable (P r f)).measurable
  have hprod : Integrable (fun ρ => f ρ * P r f ρ) (reducedLaw Q) :=
    (Lp.memLp f).integrable_mul (Lp.memLp (P r f))
  calc
    _ = ∫ ω, fr (reduce ω) * (P r f (reduce ω)).re ∂Q.measure :=
      integral_congr_ae (hkm.mono fun ω h => by rw [h]; rfl)
    _ = ∫ ρ, fr ρ * (P r f ρ).re ∂reducedLaw Q :=
      (integral_map Probability.measurable_reduce.aemeasurable
        (hfr.measurable.mul hPf).aestronglyMeasurable).symm
    _ = ∫ ρ, (f ρ * P r f ρ).re ∂reducedLaw Q :=
      integral_congr_ae (hf.mono fun ρ h => by dsimp only; rw [h, Complex.re_ofReal_mul])
    _ = _ := by
      have hre := integral_re (𝕜 := ℂ) hprod
      simpa only [RCLike.re_to_complex] using hre

end Annealed

/-- L² law of large numbers for the unforced clock of the supplied reduced law on smooth
environments: the normalized clock converges in the annealed L² sense to the clock mean. -/
theorem tendsto_unforced_clock_l2_error (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (hunforced : UnforcedAt hd Q) (hpath : PathwiseAt Q) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω 0) 0 (Y (0, ω)))
    (hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw Y ω)) :
    Tendsto (fun n : ℕ => ∫ z, ((Clock.physicalPathClock z.1 z.2 ((n + 1 : ℕ) : ℝ≥0) : ℝ) /
        ((n : ℝ) + 1) - ∫ ω, ω.2 (0 : Vec d) ∂reducedLaw Q) ^ 2
        ∂Carriers.annealedCoordinateJoint Q.measure Y hprob) atTop (𝓝 0) := by
  classical
  have : IsProbabilityMeasure Q.measure := Q.probability
  have : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  obtain ⟨K, hKm, hK, hJ⟩ := exists_unforced_reduced_kernel hd D Q hQ Y hY hprob
  rw [hJ]
  let K0 : Kernel (FieldPair d) (Path d) :=
    K.comap (fun ω => (ω, (0 : Vec d))) (measurable_id.prodMk measurable_const)
  have : IsMarkovKernel K0 := by unfold K0; infer_instance
  let m : ℝ := ∫ ω, ω.2 (0 : Vec d) ∂reducedLaw Q
  let B := Real.exp (2 * D.ellipticity) + Real.exp (-2 * D.ellipticity) + |m|
  let X : ℝ → FieldPair d × Path d → ℝ := fun u z =>
    clampedClock D.ellipticity m (translate (z.2 u.toNNReal) z.1)
  have hXc : Continuous fun p : ℝ × (FieldPair d × Path d) => X p.1 p.2 :=
    continuous_clampedClock_path D.ellipticity m
  have hXb (u : ℝ) (z : FieldPair d × Path d) : |X u z| ≤ B := abs_clampedClock_le _ m _
  -- the semigroup and the centered clock observation
  obtain ⟨P, hP, _, hmass, _, _, hrealize⟩ := id hunforced
  let fr : FieldPair d → ℝ := fun ρ => max (min (ρ.2 0) (Real.exp (2 * D.ellipticity)))
    (Real.exp (-2 * D.ellipticity)) - m
  have hfrc : Continuous fr :=
    ((((continuous_eval_const 0).comp continuous_snd).min continuous_const).max
      continuous_const).sub continuous_const
  have hfrb (ρ : FieldPair d) : ‖(fr ρ : ℂ)‖ ≤ B := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    have h1 : 0 ≤ max (min (ρ.2 0) (Real.exp (2 * D.ellipticity)))
        (Real.exp (-2 * D.ellipticity)) := (Real.exp_pos _).le.trans (le_max_right _ _)
    have h2 : max (min (ρ.2 0) (Real.exp (2 * D.ellipticity))) (Real.exp (-2 * D.ellipticity)) ≤
        Real.exp (2 * D.ellipticity) + Real.exp (-2 * D.ellipticity) :=
      max_le ((min_le_right _ _).trans (le_add_of_nonneg_right (Real.exp_pos _).le))
        (le_add_of_nonneg_left (Real.exp_pos _).le)
    calc |fr ρ| ≤ |max (min (ρ.2 0) (Real.exp (2 * D.ellipticity)))
            (Real.exp (-2 * D.ellipticity))| + |m| := abs_sub _ _
      _ ≤ B := by rw [abs_of_nonneg h1]; linarith
  have hfm : MemLp (fun ρ => (fr ρ : ℂ)) 2 (reducedLaw Q) :=
    MemLp.of_bound (Complex.continuous_ofReal.comp hfrc).aestronglyMeasurable B
      (ae_of_all _ hfrb)
  let f : Lp ℂ 2 (reducedLaw Q) := hfm.toLp _
  have hf : f =ᵐ[reducedLaw Q] fun ρ => ((fr ρ : ℝ) : ℂ) := hfm.coeFn_toLp
  have hfr_ae : ∀ᵐ ρ ∂reducedLaw Q, fr ρ = ρ.2 0 - m := by
    apply (ae_map_iff Probability.measurable_reduce.aemeasurable
      (measurableSet_eq_fun hfrc.measurable
        (Clock.continuous_clockAtOrigin.measurable.sub measurable_const))).mpr
    filter_upwards [Q.regular] with ω hω
    have hb := clockDensity_bounds ω 0 D.ellipticity (hω.2.1 0)
    change max (min (clockDensity ω 0) _) _ - m = clockDensity ω 0 - m
    rw [min_eq_left hb.2, max_eq_left hb.1]
  have hf0 : (∫ ρ, f ρ ∂reducedLaw Q) = 0 := by
    rw [integral_congr_ae hf, integral_complex_ofReal, integral_congr_ae hfr_ae,
      integral_sub (c20_clock_integrable Q) (integrable_const m), integral_const]
    simp [m]
  have hlim := c20_generator_range_closure_average_tendsto_zero hP (fun t g => (hmass t g).1)
    (c20_mean_zero_mem_generator_range_closure d hd D.ellipticity D.dependenceRange Q
      hunforced f hf0)
  -- the pairing with the centered observation
  let ℓ : Lp ℂ 2 (reducedLaw Q) →L[ℂ] ℂ :=
    innerSL ℂ (complexL2Conjugation (reducedLaw Q) f)
  have hℓ (g : Lp ℂ 2 (reducedLaw Q)) : ℓ g = ∫ ρ, f ρ * g ρ ∂reducedLaw Q :=
    inner_complexL2Conjugation_eq_integral_mul _ f g
  let g : ℝ → Lp ℂ 2 (reducedLaw Q) := fun r => P r.toNNReal f
  have hg : Continuous g := (hP.2.2.1 f).comp continuous_real_toNNReal
  -- two-time correlations
  have htwo (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
      ∫ z, X u z * X v z ∂(Q.measure ⊗ₘ K0) = (ℓ (g |v - u|)).re := by
    have hcase (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) :
        ∫ z, X a z * X b z ∂(Q.measure ⊗ₘ K0) = (ℓ (g (b - a))).re := by
      rw [annealed_clampedClock_mul_of_le hd D Q hQ hunforced hpath hK m
          (Real.toNNReal_le_toNNReal hab),
        integral_clampedClock_mul_kernelClockMean hd D Q hQ hunforced hpath hK m P hrealize f
          hf, hℓ]
      change (∫ ρ, f ρ * P (b.toNNReal - a.toNNReal) f ρ ∂reducedLaw Q).re =
        (∫ ρ, f ρ * P (b - a).toNNReal f ρ ∂reducedLaw Q).re
      have e : (b - a).toNNReal = b.toNNReal - a.toNNReal := by
        apply NNReal.eq
        rw [Real.coe_toNNReal _ (sub_nonneg.2 hab),
          NNReal.coe_sub (Real.toNNReal_le_toNNReal hab), Real.coe_toNNReal _ (ha.trans hab),
          Real.coe_toNNReal _ ha]
      rw [e]
    rcases le_total u v with huv | hvu
    · rw [hcase u v hu huv, abs_of_nonneg (sub_nonneg.2 huv)]
    · simp_rw [mul_comm (X u _)]
      rw [hcase v u hv hvu, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hvu)]
  -- the square of the centered clock
  have hT (n : ℕ) : ∫ z, ((Clock.physicalPathClock z.1 z.2 ((n + 1 : ℕ) : ℝ≥0) : ℝ) /
        ((n : ℝ) + 1) - m) ^ 2 ∂(Q.measure ⊗ₘ K0) =
      ((n : ℝ) + 1)⁻¹ ^ 2 * ∫ u in (0 : ℝ)..((n : ℝ) + 1),
        ∫ v in (0 : ℝ)..((n : ℝ) + 1), (ℓ (g |v - u|)).re := by
    have hT0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hreg : ∀ᵐ z ∂(Q.measure ⊗ₘ K0), IsRegular D.ellipticity z.1 := by
      have h := Q.regular
      rw [← Measure.fst_compProd (μ := Q.measure) (κ := K0)] at h
      exact ae_of_ae_map measurable_fst.aemeasurable h
    have hpt : ∀ᵐ z ∂(Q.measure ⊗ₘ K0),
        ((Clock.physicalPathClock z.1 z.2 ((n + 1 : ℕ) : ℝ≥0) : ℝ) / ((n : ℝ) + 1) - m) ^ 2 =
          ((n : ℝ) + 1)⁻¹ ^ 2 * ∫ u in (0 : ℝ)..((n : ℝ) + 1),
            ∫ v in (0 : ℝ)..((n : ℝ) + 1), X u z * X v z := by
      filter_upwards [hreg] with z hz
      have hA := physicalPathClock_sub_eq_integral m hz z.2 ((n + 1 : ℕ) : ℝ≥0)
      have hcast : (((n + 1 : ℕ) : ℝ≥0) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
      rw [hcast] at hA
      rw [← sq_intervalIntegral_eq, ← hA]
      field_simp
    rw [integral_congr_ae hpt, integral_const_mul]
    congr 1
    have hmeas2 : Measurable fun p : ℝ × ℝ × (FieldPair d × Path d) =>
        X p.1 p.2.2 * X p.2.1 p.2.2 :=
      ((hXc.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))).mul
        (hXc.comp ((continuous_fst.comp continuous_snd).prodMk
          (continuous_snd.comp continuous_snd)))).measurable
    have hbound2 (u v : ℝ) (z : FieldPair d × Path d) : |X u z * X v z| ≤ B * B := by
      rw [abs_mul]
      exact mul_le_mul (hXb u z) (hXb v z) (abs_nonneg _) ((abs_nonneg _).trans (hXb u z))
    have hinner (u : ℝ) : Measurable fun p : ℝ × (FieldPair d × Path d) => X u p.2 * X p.1 p.2 :=
      ((hXc.comp (continuous_const.prodMk continuous_snd)).mul hXc).measurable
    rw [integral_intervalIntegral_comm _ (F := fun u z => ∫ v in (0 : ℝ)..((n : ℝ) + 1),
        X u z * X v z) (measurable_intervalIntegral_param (F := fun u v z => X u z * X v z)
          hmeas2 hT0.le) (C := B * B *
          ((n : ℝ) + 1)) (fun u z => by
            have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0)
              (b := (n : ℝ) + 1) (C := B * B) (f := fun v => X u z * X v z)
              (fun v _ => by simpa only [Real.norm_eq_abs] using hbound2 u v z)
            simpa only [Real.norm_eq_abs, sub_zero, abs_of_pos hT0] using h) hT0.le]
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [Set.uIcc_of_le hT0.le] at hu
    rw [integral_intervalIntegral_comm _ (hinner u) (fun v z => hbound2 u v z) hT0.le]
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [Set.uIcc_of_le hT0.le] at hv
    exact htwo u v hu.1 hv.1
  -- the semigroup averages
  have hδ (w : ℝ) (hw : 0 ≤ w) : ‖∫ r in (0 : ℝ)..w, g r‖ ≤ ‖f‖ * w := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := w)
      (C := ‖f‖) (f := g) (fun r _ => (hmass r.toNNReal f).1)
    simpa only [sub_zero, abs_of_nonneg hw, mul_comm] using h
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  have hℓ0 : 0 ≤ ‖ℓ‖ := norm_nonneg _
  set ε₁ := ε / (2 * (‖ℓ‖ + 1)) with hε₁
  have hε₁pos : 0 < ε₁ := div_pos hε (by positivity)
  obtain ⟨W, hW⟩ := eventually_atTop.1 ((Metric.tendsto_nhds.1 hlim) ε₁ hε₁pos)
  have hδW (w : ℝ) (hw : 0 ≤ w) : ‖∫ r in (0 : ℝ)..w, g r‖ ≤ ε₁ * w + ‖f‖ * W := by
    have hfW : 0 ≤ ‖f‖ * W := mul_nonneg (norm_nonneg f) W.coe_nonneg
    rcases hw.eq_or_lt with hw0 | hwpos
    · subst hw0
      simp only [intervalIntegral.integral_same, norm_zero, mul_zero, zero_add]
      exact hfW
    by_cases hwW : (W : ℝ) ≤ w
    · have h := hW w.toNNReal (by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hw]; exact hwW)
      rw [dist_zero_right, Real.coe_toNNReal _ hw, norm_smul, norm_inv, Real.norm_eq_abs,
        abs_of_pos hwpos] at h
      have h' : ‖∫ r in (0 : ℝ)..w, g r‖ < w * ε₁ := (inv_mul_lt_iff₀ hwpos).1 h
      nlinarith
    · push Not at hwW
      have := hδ w hw
      have h2 : ‖f‖ * w ≤ ‖f‖ * W := mul_le_mul_of_nonneg_left hwW.le (norm_nonneg f)
      nlinarith [mul_nonneg hε₁pos.le hw]
  obtain ⟨N, hN⟩ := exists_nat_gt (4 * ‖ℓ‖ * ‖f‖ * W / ε)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_zero_right, hT n, Real.norm_eq_abs]
  have hT0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  set T : ℝ := (n : ℝ) + 1 with hTdef
  have hinnerb (u : ℝ) (hu : u ∈ Set.uIoc 0 T) :
      ‖∫ v in (0 : ℝ)..T, (ℓ (g |v - u|)).re‖ ≤ ‖ℓ‖ * (ε₁ * T + 2 * (‖f‖ * W)) := by
    rw [Set.uIoc_of_le hT0.le] at hu
    have hre : (∫ v in (0 : ℝ)..T, (ℓ (g |v - u|)).re) =
        (∫ v in (0 : ℝ)..T, ℓ (g |v - u|)).re := by
      have h := intervalIntegral.intervalIntegral_re (𝕜 := ℂ) (f := fun v => ℓ (g |v - u|)) (a := 0) (b := T)
        (μ := volume) ((ℓ.continuous.comp (hg.comp
          (continuous_id.sub continuous_const).abs)).intervalIntegrable 0 T)
      simpa only [RCLike.re_to_complex] using h
    rw [hre, Real.norm_eq_abs]
    refine (Complex.abs_re_le_norm _).trans ((norm_intervalIntegral_dist_le hg ℓ hu.1.le hu.2).trans ?_)
    refine mul_le_mul_of_nonneg_left ?_ hℓ0
    have h1 := hδW u hu.1.le
    have h2 := hδW (T - u) (sub_nonneg.2 hu.2)
    exact (add_le_add h1 h2).trans (le_of_eq (by ring))
  have hout := intervalIntegral.norm_integral_le_of_norm_le_const hinnerb
  rw [sub_zero, abs_of_pos hT0, Real.norm_eq_abs] at hout
  rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
  calc T⁻¹ ^ 2 * |∫ u in (0 : ℝ)..T, ∫ v in (0 : ℝ)..T, (ℓ (g |v - u|)).re|
      ≤ T⁻¹ ^ 2 * (‖ℓ‖ * (ε₁ * T + 2 * (‖f‖ * W)) * T) :=
        mul_le_mul_of_nonneg_left hout (sq_nonneg _)
    _ = ‖ℓ‖ * ε₁ + 2 * ‖ℓ‖ * ‖f‖ * W / T := by field_simp
    _ < ε := by
      have hTN : 4 * ‖ℓ‖ * ‖f‖ * W / ε < T := by
        have : (N : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      have h1 : ‖ℓ‖ * ε₁ < ε / 2 := by
        rw [hε₁, mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith
      have h2 : 2 * ‖ℓ‖ * ‖f‖ * W / T ≤ ε / 2 := by
        rw [div_le_iff₀ hT0]
        rw [div_lt_iff₀ hε] at hTN
        nlinarith [mul_nonneg (mul_nonneg hℓ0 (norm_nonneg f)) W.coe_nonneg]
      linarith

end EinsteinFull.Blueprint
