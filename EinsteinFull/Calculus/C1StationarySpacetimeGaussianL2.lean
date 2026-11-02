import EinsteinFull.Calculus.C1StationaryGaussianOrbitL2
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.AKM
/-- Stationary space-time L² data have Gaussian-weighted physical L² orbits. -/
theorem ae_stationary_spacetime_orbit_gaussian_memLp
    (d : ℕ) (hd : 2 ≤ d) (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) (T : ℝ) (hT : 0 ≤ T)
    (f : ℝ × FieldPair d → ℂ) (hf : Measurable f)
    (hfi : Integrable (fun p : ℝ × FieldPair d => ‖f p‖ ^ 2)
      ((volume.restrict (Set.Icc 0 T)).prod Q)) :
    ∀ᵐ ω ∂Q, ∀ r : ℝ, 0 < r →
      MemLp (fun p : ℝ × Vec d => (Real.exp (-euclideanSq p.2/r) : ℂ) *
        f (p.1, translate p.2 ω)) 2
        ((volume.restrict (Set.Icc 0 T)).prod volume) := by
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hs : Continuous (euclideanSq : Vec d → ℝ) := by
    unfold euclideanSq dot
    fun_prop
  have hmeas (r : ℝ) (ω : FieldPair d) : AEStronglyMeasurable
      (fun p : ℝ × Vec d => (Real.exp (-euclideanSq p.2/r) : ℂ) * f (p.1, translate p.2 ω)) ((volume.restrict (Set.Icc 0 T)).prod volume) := by
    apply Measurable.aestronglyMeasurable
    exact (Complex.measurable_ofReal.comp
      (Real.continuous_exp.comp ((hs.comp continuous_snd).neg.div_const r)).measurable).mul
      (hf.comp (measurable_fst.prodMk
        (Probability.continuous_translate.measurable.comp
          (measurable_snd.prodMk measurable_const))))
  have hnorm (r : ℝ) (ω : FieldPair d) (p : ℝ × Vec d) :
      ‖(Real.exp (-euclideanSq p.2/r) : ℂ) * f (p.1, translate p.2 ω)‖ ^ 2 =
        Real.exp (-(2/r) * euclideanSq p.2) * ‖f (p.1, translate p.2 ω)‖ ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow]
    rw [← Real.exp_nat_mul]
    congr 2
    push_cast
    ring
  have hn (n : ℕ) : ∀ᵐ ω ∂Q,
      MemLp (fun p : ℝ × Vec d => (Real.exp (-euclideanSq p.2/((n:ℝ)+d)) : ℂ) *
        f (p.1, translate p.2 ω)) 2 ((volume.restrict (Set.Icc 0 T)).prod volume) := by
    let κ : ℝ := 2 / ((n : ℝ)+d)
    have hκ : 0 < κ := by dsimp only [κ]; positivity
    have hg : Integrable (fun x : Vec d => Real.exp (-κ * euclideanSq x)) := by
      have hp : Integrable (fun x : Vec d => ∏ j : Fin d, Real.exp (-κ * x j ^ 2))
          (Measure.pi fun _ : Fin d => (volume : Measure ℝ)) :=
        Integrable.fintype_prod (fun _ => integrable_exp_neg_mul_sq hκ)
      convert hp using 1
      funext x
      rw [← Real.exp_sum]
      congr 1
      simp only [euclideanSq, dot, ← Finset.mul_sum, sq]
    let g : (ℝ × Vec d) × FieldPair d → ℝ := fun p =>
      Real.exp (-κ * euclideanSq p.1.2) * ‖f (p.1.1, translate p.1.2 p.2)‖ ^ 2
    have hfm : Measurable (fun p : (ℝ × Vec d) × FieldPair d =>
        f (p.1.1, translate p.1.2 p.2)) :=
      hf.comp ((measurable_fst.comp measurable_fst).prodMk
        (Probability.continuous_translate.measurable.comp
          ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
    have hgm : Measurable g :=
      (Real.continuous_exp.comp
        ((hs.comp (continuous_snd.comp continuous_fst)).const_mul (-κ))).measurable.mul
        (hfm.norm.pow_const 2)
    have heq (p : ℝ × Vec d) : (∫ ω, ‖g (p, ω)‖ ∂Q) =
        Real.exp (-κ * euclideanSq p.2) * ∫ ω, ‖f (p.1, ω)‖ ^ 2 ∂Q := by
      have hm := measurePreserving_translate Q hQ p.2
      simp only [g, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        abs_pow, abs_norm, integral_const_mul]
      congr 1
      exact (integral_map hm.measurable.aemeasurable
        ((hf.comp (measurable_const.prodMk measurable_id)).norm.pow_const 2).aestronglyMeasurable).symm.trans
        (congrArg (fun μ : Measure (FieldPair d) => ∫ ω, ‖f (p.1, ω)‖ ^ 2 ∂μ) hm.map_eq)
    have hgi : Integrable g (((volume.restrict (Set.Icc 0 T)).prod volume).prod Q) := by
      apply (integrable_prod_iff hgm.aestronglyMeasurable).mpr
      constructor
      · filter_upwards [Measure.quasiMeasurePreserving_fst.ae hfi.prod_right_ae] with p hp
        exact ((measurePreserving_translate Q hQ p.2).integrable_comp_of_integrable hp).const_mul
          (Real.exp (-κ * euclideanSq p.2))
      · have ht : Integrable (fun t => ∫ ω, ‖f (t, ω)‖ ^ 2 ∂Q)
            (volume.restrict (Set.Icc 0 T)) := by
          simpa only [Real.norm_eq_abs, abs_pow, abs_norm] using hfi.integral_norm_prod_left
        simpa only [heq, mul_comm] using ht.mul_prod hg
    filter_upwards [hgi.prod_left_ae] with ω hω
    apply (memLp_two_iff_integrable_sq_norm (hmeas _ ω)).mpr
    simpa only [hnorm, κ, g] using hω
  filter_upwards [ae_all_iff.mpr hn] with ω hω
  intro r hr
  obtain ⟨n, hnT⟩ := exists_nat_gt (r + T)
  have hn : r < (n : ℝ) := lt_of_le_of_lt (le_add_of_nonneg_right hT) hnT
  apply (hω n).mono (hmeas r ω)
  apply ae_of_all
  intro p
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  have hx : 0 ≤ euclideanSq p.2 := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun j _ => mul_self_nonneg (p.2 j)
  have hh : euclideanSq p.2 / ((n:ℝ)+d) ≤ euclideanSq p.2 / r :=
    div_le_div_of_nonneg_left hx hr (by linarith)
  simpa only [neg_div] using neg_le_neg hh

example : type_of% @ae_stationary_spacetime_orbit_gaussian_memLp =
    ∀ (d : ℕ) (hd : 2 ≤ d) (Q : Measure (FieldPair d)) (_ : IsProbabilityMeasure Q)
    (hQ : IsStationary Q) (T : ℝ) (hT : 0 ≤ T)
    (f : ℝ × FieldPair d → ℂ) (hf : Measurable f)
    (hfi : Integrable (fun p : ℝ × FieldPair d => ‖f p‖ ^ 2)
      ((volume.restrict (Set.Icc 0 T)).prod Q)),
    ∀ᵐ ω ∂Q, ∀ r : ℝ, 0 < r →
      MemLp (fun p : ℝ × Vec d => (Real.exp (-euclideanSq p.2/r) : ℂ) *
        f (p.1, translate p.2 ω)) 2
        ((volume.restrict (Set.Icc 0 T)).prod volume) := rfl

#print axioms ae_stationary_spacetime_orbit_gaussian_memLp
#lint

run_cmd do
  let env ← Lean.getEnv
  let mut checked : Nat := 0
  for (n, _) in env.constants.toList do
    if (env.getModuleIdxFor? n).isNone then
      let axs ← Lean.collectAxioms n
      unless axs.all (fun a => #[`propext, `Classical.choice, `Quot.sound].contains a) do
        throwError m!"nonstandard axioms for {n}: {axs}"
      checked := checked + 1
  Lean.logInfo m!"C1 all-owned-and-generated transitive axiom audit passed: {checked} declarations"

end EinsteinFull.Blueprint
