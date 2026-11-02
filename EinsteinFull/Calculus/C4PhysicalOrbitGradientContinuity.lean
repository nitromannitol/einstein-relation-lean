import EinsteinFull.Calculus.C4PhysicalGeneratorGradientBound
import EinsteinFull.Calculus.C3PhysicalGeneratorLinearity
import EinsteinFull.Calculus.PhysicalH1ClosedGraphSupport
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.AKM
private theorem orbitH1_sub {d : ℕ}
    (u v : Lp ℂ 2 (volume : Measure (Vec d)))
    (G H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hu : IsPhysicalH1Graph volume (Or.inl rfl) u G)
    (hv : IsPhysicalH1Graph volume (Or.inl rfl) v H) :
    IsPhysicalH1Graph volume (Or.inl rfl) (u - v) (fun j => G j - H j) := by
  have hneg {j : Fin d} {f g : Vec d → ℝ}
      (h : HasWeakPartialDerivative univ j f g) :
      HasWeakPartialDerivative univ j (fun x => -f x) (fun x => -g x) := by
    refine ⟨fun x hx => (h.1 x hx).neg, fun x hx => (h.2.1 x hx).neg, ?_⟩
    intro φ hφ
    simp only [neg_mul, integral_neg, h.2.2 φ hφ]
  apply (isPhysicalH1Graph_iff_representatives volume (Or.inl rfl) _ _
    (fun x => u x - v x) (fun j x => G j x - H j x)
    (Lp.coeFn_sub _ _) (fun _ => Lp.coeFn_sub _ _)).mpr
  constructor
  · intro j
    simpa only [sub_eq_add_neg, Complex.add_re, Complex.neg_re] using
      Correctors.hasWeakPartialDerivative_add (hu.1 j) (hneg (hv.1 j))
  · intro j
    simpa only [sub_eq_add_neg, Complex.add_im, Complex.neg_im] using
      Correctors.hasWeakPartialDerivative_add (hu.2 j) (hneg (hv.2 j))

/-- A continuous orbit in the physical generator graph has continuous weak gradients. -/
theorem physical_generator_orbit_continuous_gradient
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (u g : ℝ → Lp ℂ 2 (volume : Measure (Vec d)))
    (hu : Continuous u) (hg : Continuous g)
    (hpair : ∀ t, IsPhysicalComplexGeneratorPair a i ζ (u t) (g t)) :
    ∃ G : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ t, IsPhysicalH1Graph volume (Or.inl rfl) (u t) (G t)) ∧
      ∀ j, Continuous (fun t => G t j) := by
  classical
  have hex := hpair
  choose G hG hweak using hex
  refine ⟨G, hG, fun j => continuous_iff_continuousAt.mpr fun s => ?_⟩
  have hdiff (t : ℝ) : IsPhysicalComplexGeneratorPair a i ζ (u t - u s) (g t - g s) := by
    simpa only [one_smul, neg_one_smul, sub_eq_add_neg] using
      physical_complex_generator_graph_linear_combination a i ζ 1 (-1) ha (hpair t) (hpair s)
  have hb (t : ℝ) : ‖G t j - G s j‖ ^ 2 ≤
      4*Λ*‖u t - u s‖*‖g t - g s‖ +
        4*((d : ℝ)+1)^2*Λ^4*‖ζ‖^2*‖u t - u s‖^2 := by
    obtain ⟨H, hH, hb⟩ := physical_complex_generator_gradient_bound a i ζ ha hΛ hA (hdiff t)
    have he := physicalH1Graph_gradient_unique volume (Or.inl rfl) (u t - u s)
      H (fun k => G t k - G s k) hH (orbitH1_sub _ _ _ _ (hG t) (hG s))
    rw [he] at hb
    exact (Finset.single_le_sum (fun k _ => sq_nonneg ‖G t k - G s k‖)
      (Finset.mem_univ j)).trans hb
  have hlimu : Tendsto (fun t => ‖u t - u s‖) (𝓝 s) (𝓝 0) := by
    simpa only [sub_self, norm_zero] using ((hu.tendsto s).sub (tendsto_const_nhds (x := u s))).norm
  have hlimg : Tendsto (fun t => ‖g t - g s‖) (𝓝 s) (𝓝 0) := by
    simpa only [sub_self, norm_zero] using ((hg.tendsto s).sub (tendsto_const_nhds (x := g s))).norm
  have hlim : Tendsto (fun t => 4*Λ*‖u t - u s‖*‖g t - g s‖ +
      4*((d : ℝ)+1)^2*Λ^4*‖ζ‖^2*‖u t - u s‖^2) (𝓝 s) (𝓝 0) := by
    simpa only [mul_zero, zero_mul, zero_pow (by decide : 2 ≠ 0), zero_add] using
      ((hlimu.const_mul (4*Λ)).mul hlimg).add
        ((hlimu.pow 2).const_mul (4*((d : ℝ)+1)^2*Λ^4*‖ζ‖^2))
  have hsquare := squeeze_zero (fun t => sq_nonneg ‖G t j - G s j‖) hb hlim
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsquare
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsqrt
end EinsteinFull.Blueprint
