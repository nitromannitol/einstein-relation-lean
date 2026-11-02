import EinsteinFull.Calculus.SbxBShiftedHarnackChainR12
import EinsteinFull.Calculus.SbxBPointwiseHarnackScalingR12
import EinsteinFull.Calculus.SbxBUnitPointwiseHarnackClosureR14
import EinsteinFull.Calculus.C18TubeCaloricTimeTranslation

open EinsteinRelation MeasureTheory Filter EinsteinFull.External.Source.GMP
open EinsteinFull.Blueprint.TubeProbability EinsteinFull.Blueprint.SbxS3UniformCrossHeat
open scoped Topology InnerProductSpace NNReal

namespace EinsteinFull.Calculus

/-- The symmetric heat series for the actual weighted Dirichlet resolution. -/
noncomputable def bSpectralRowR14 {d : ℕ} {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    {R : ℝ} (s : DirichletSpectralResolution ρ α R) (t : ℝ) (x y : Vec d) : ℝ :=
  ∑' i, Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x * s.eigenfunction i y

/-- A native variational spectrum has the early/late comparison, without an
initial-delta or fundamental-solution hypothesis. The constants precede the
ball and coefficients; the gradient is common to every positive strip. -/
theorem b_spectral_row_harnack_r14 (d : ℕ) (hd : 2 ≤ d) (κ : ℝ) (hκ : 0 < κ) :
    ∃ δ H : ℝ, 0 < δ ∧ 0 < H ∧ ∀ (R : ℝ) (hR : 0 < R)
      (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
      (s : DirichletSpectralResolution ρ α R)
      (_hs : Tendsto s.eigenvalue atTop atTop)
      (w : ℕ → DirichletHilbertSpace (d := d) R hR),
      (∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (hell.2.2 x).2.1) (w n)) →
      (∀ n v, (∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (fun i => (w n).val (some i) x))
          (fun i => v.val (some i) x)) = s.eigenvalue n * inner ℝ
        (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1) (w n))
        (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1) v)) →
      ∃ G : ℝ → Vec d → Vec d → Vec d,
        (∀ y ∈ sourceBall (0 : Vec d) R, ∀ a b : ℝ, 0 < a → a < b →
          IsWeightedCaloric ρ α (Set.Ioo a b) (sourceBall 0 R)
            (fun z => bSpectralRowR14 s z.1 z.2 y) (fun z => G z.1 z.2 y)) ∧
        ∀ (x y : Vec d) (r u : ℝ), 0 < r →
          sourceBall x (2*r) ⊆ sourceBall 0 R → y ∈ sourceBall 0 R →
          0 < u → u ≤ δ*r^2 → euclideanSq (x-y) ≤ u →
          bSpectralRowR14 s (2*u) x x ≤ H * bSpectralRowR14 s (4*u) x y := by
  obtain ⟨H, hH, hchain⟩ :=
    b_shifted_pointwise_harnack_of_scaled_unit d κ 1 0 (by norm_num) (by norm_num)
      (b_pointwise_harnack_chain_step_of_unit d κ (b_unit_pointwise_harnack_r14 d hd κ hκ))
  refine ⟨1/16, H, by norm_num, hH, ?_⟩
  intro R hR ρ α hell s hs w hb hvar
  obtain ⟨G, hG⟩ := spectral_heat_global_positive_strip_gradient hd hκ hell R hR s hs w hb hvar
  refine ⟨G, ?_, ?_⟩
  · intro y hy a b ha hab
    exact (hG y hy a b ha hab).1
  · intro x y r u hr hball hy hu hut hdist
    have hx : x ∈ sourceBall (0 : Vec d) R := hball (by
      change euclideanNorm (x-x) < 2*r
      simpa [euclideanNorm, euclideanSq, dot] using (show 0 < 2*r by positivity))
    have hdist' : euclideanNorm (y-x)^2 ≤ u := by
      rw [show y-x = -(x-y) by abel, Entropy.euclideanNorm_neg',
        ← TimeChange.euclideanSq_eq_sq_euclideanNorm]
      exact hdist
    have hsq : 0 ≤ Real.sqrt u := Real.sqrt_nonneg _
    have hsq2 : (Real.sqrt u)^2 = u := Real.sq_sqrt hu.le
    have hsq4 : Real.sqrt (4*u) = 2*Real.sqrt u := by
      have h1 : 0 ≤ Real.sqrt (4*u) := Real.sqrt_nonneg _
      have h2 : (Real.sqrt (4*u))^2 = 4*u := Real.sq_sqrt (by positivity)
      nlinarith
    have hnorm : 0 ≤ euclideanNorm (y-x) := Real.sqrt_nonneg _
    have hdist'' : euclideanNorm (y-x) ≤ Real.sqrt u := by nlinarith
    have hmargin : euclideanNorm (y-x) + 3*Real.sqrt (4*u) ≤ 2*r := by
      rw [hsq4]
      nlinarith [sq_nonneg (r - 4*Real.sqrt u)]
    have hball' : sourceBall y ((1+0+2)*Real.sqrt (4*u)) ⊆ sourceBall 0 R := by
      intro z hz
      apply hball
      change euclideanNorm (z-x) < 2*r
      change euclideanNorm (z-y) < (1+0+2)*Real.sqrt (4*u) at hz
      have htri := TimeChange.euclideanNorm_add_le (z-y) (y-x)
      have heq : z-x = (z-y)+(y-x) := by ext i; simp
      rw [heq]
      nlinarith
    let v : ℝ × Vec d → ℝ := fun p => bSpectralRowR14 s (u+p.1) p.2 x
    let F : ℝ × Vec d → Vec d := fun p => G (u+p.1) p.2 x
    have hc : IsWeightedCaloric ρ α (Set.Ioo 0 (2*(4*u))) (sourceBall 0 R) v F := by
      have hhcal := (hG x hx u (9*u) hu (by linarith)).1
      have hc' := c18_weighted_caloric_time_translate ρ α 0 (8*u) u
        (sourceBall 0 R) (fun p => bSpectralRowR14 s p.1 p.2 x)
        (fun p => G p.1 p.2 x) (by
          convert hhcal using 1
          all_goals congr 1
          all_goals ring)
      convert hc' using 1 <;> try { congr 1 <;> ring }
    have hcont : ContinuousOn v (Set.Ioo 0 (2*(4*u)) ×ˢ sourceBall 0 R) := by
      have hcmap : ContinuousOn (fun p : ℝ × Vec d => (u+p.1,p.2))
          (Set.Ioo 0 (2*(4*u)) ×ˢ sourceBall 0 R) :=
        ((continuous_const.add continuous_fst).prodMk continuous_snd).continuousOn
      have hmaps : Set.MapsTo (fun p : ℝ × Vec d => (u+p.1,p.2))
          (Set.Ioo 0 (2*(4*u)) ×ˢ sourceBall 0 R)
          (Set.Ioi 0 ×ˢ closure (sourceBall (0 : Vec d) R)) := by
        intro p hp
        exact ⟨by change 0 < u+p.1; linarith [hp.1.1], subset_closure hp.2⟩
      simpa [v, bSpectralRowR14, Function.comp_def] using
        (spectral_heat_row_continuousOn_closedBall hd hκ hell hR s hs x hx).comp hcmap hmaps
    have hnonneg : ∀ p ∈ Set.Ioo 0 (2*(4*u)) ×ˢ sourceBall 0 R, 0 ≤ v p := by
      intro p hp
      have ht : 0 < u+p.1 := by linarith [hp.1.1]
      simpa only [v, bSpectralRowR14, Real.coe_toNNReal _ ht.le] using
        (spectral_heat_kernel_nonneg_of_variational hd hκ hell R hR s hs w hb hvar).2
          (u+p.1).toNNReal (by simpa only [Real.coe_toNNReal _ ht.le] using ht) p.2 hp.2 x hx
    have hxy : euclideanNorm (x-y) ≤ (1+0)*Real.sqrt (4*u) := by
      rw [show x-y = -(y-x) by abel, Entropy.euclideanNorm_neg', hsq4]
      nlinarith
    have h := hchain R hR ρ α hell (4*u) (by positivity) v F hc hcont hnonneg
      x hx y hy hball' hxy
    have h' : bSpectralRowR14 s (2*u) x x ≤ H * bSpectralRowR14 s (4*u) y x := by
      have ht1 : u + (4*u)/4 = 2*u := by ring
      have ht2 : u + 3*(4*u)/4 = 4*u := by ring
      simpa only [v, ht1, ht2] using h
    have hsym : bSpectralRowR14 s (4*u) y x = bSpectralRowR14 s (4*u) x y := by
      unfold bSpectralRowR14
      apply tsum_congr
      intro n
      ring
    simpa only [hsym] using h'

#print axioms b_spectral_row_harnack_r14

end EinsteinFull.Calculus
