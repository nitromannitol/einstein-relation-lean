import Mathlib.Algebra.Order.Chebyshev
import EinsteinFull.Calculus.PhysicalComplexEvolution
import EinsteinFull.Calculus.PhysicalH1ClosedGraphSupport
import EinsteinFull.Calculus.C1CrudeEnergyLargeTime
import EinsteinFull.Calculus.C4PhysicalOrbitGradientContinuity

open MeasureTheory Filter
open scoped NNReal ENNReal BigOperators Topology

namespace EinsteinFull
open EinsteinRelation

/-- The difference of two physical generator graphs, tested against the same
weak gradient, is the literal difference of their coefficient forms. -/
theorem s4_physical_generator_coefficient_difference {d : ℕ}
    (a b : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (hb : ∀ j k, MemLp (fun x => (b x j k : ℂ)) ∞ volume)
    (f ga gb v : Lp ℂ 2 (volume : Measure (Vec d)))
    (G H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    (hH : IsPhysicalH1Graph volume (Or.inl rfl) v H)
    (hga : IsPhysicalComplexGeneratorPair a i ζ f ga)
    (hgb : IsPhysicalComplexGeneratorPair b i ζ f gb) :
    (∫ x, ga x * v x) - (∫ x, gb x * v x) =
      -(1 / 2 : ℂ) * (∫ x, ∑ j, ∑ k,
        ((a x j k : ℂ) - (b x j k : ℂ)) * G k x * H j x) +
      ζ * (∫ x, (∑ j, ((a x j i : ℂ) - (b x j i : ℂ)) * G j x) * v x) := by
  obtain ⟨Ga, hGa, hfa⟩ := hga
  obtain ⟨Gb, hGb, hfb⟩ := hgb
  rw [physicalH1Graph_gradient_unique volume (Or.inl rfl) f Ga G hGa hG] at hfa
  rw [physicalH1Graph_gradient_unique volume (Or.inl rfl) f Gb G hGb hG] at hfb
  have hp (c : Vec d → Mat d)
      (hc : ∀ j k, MemLp (fun x => (c x j k : ℂ)) ∞ volume) :
      Integrable (fun x => ∑ j, ∑ k, (c x j k : ℂ) * G k x * H j x) volume := by
    apply integrable_finsetSum
    intro j _
    apply integrable_finsetSum
    intro k _
    exact ((hc j k).mul (r := 2) (Lp.memLp (G k))).integrable_mul (Lp.memLp (H j))
  have hd (c : Vec d → Mat d)
      (hc : ∀ j k, MemLp (fun x => (c x j k : ℂ)) ∞ volume) :
      Integrable (fun x => (∑ j, (c x j i : ℂ) * G j x) * v x) volume := by
    have : Integrable (fun x => ∑ j, (c x j i : ℂ) * G j x * v x) volume := by
      apply integrable_finsetSum
      intro j _
      exact ((hc j i).mul (r := 2) (Lp.memLp (G j))).integrable_mul (Lp.memLp v)
    simpa only [Finset.sum_mul] using this
  rw [hfa v H hH, hfb v H hH]
  have he1 : (fun x => ∑ j, ∑ k, ((a x j k : ℂ) - (b x j k : ℂ)) * G k x * H j x) =
      (fun x => (∑ j, ∑ k, (a x j k : ℂ) * G k x * H j x) -
        (∑ j, ∑ k, (b x j k : ℂ) * G k x * H j x)) := by
    funext x
    simp only [sub_mul, Finset.sum_sub_distrib]
  have he2 : (fun x => (∑ j, ((a x j i : ℂ) - (b x j i : ℂ)) * G j x) * v x) =
      (fun x => (∑ j, (a x j i : ℂ) * G j x) * v x -
        (∑ j, (b x j i : ℂ) * G j x) * v x) := by
    funext x
    simp only [sub_mul, Finset.sum_sub_distrib]
  rw [he1, he2, integral_sub (hp a ha) (hp b hb), integral_sub (hd a ha) (hd b hb)]
  ring


/-- The corresponding comparison for the bilinear transpose uses the
transposed principal coefficients and the divergence-form drift. -/
theorem s4_physical_transpose_coefficient_difference {d : ℕ}
    (a b : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (hb : ∀ j k, MemLp (fun x => (b x j k : ℂ)) ∞ volume)
    (f ga gb v : Lp ℂ 2 (volume : Measure (Vec d)))
    (G H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    (hH : IsPhysicalH1Graph volume (Or.inl rfl) v H)
    (hga : IsPhysicalComplexTransposeGeneratorPair a i ζ f ga)
    (hgb : IsPhysicalComplexTransposeGeneratorPair b i ζ f gb) :
    (∫ x, ga x * v x) - (∫ x, gb x * v x) =
      -(1 / 2 : ℂ) * (∫ x, ∑ j, ∑ k,
        ((a x k j : ℂ) - (b x k j : ℂ)) * G k x * H j x) +
      ζ * (∫ x, f x * (∑ j, ((a x j i : ℂ) - (b x j i : ℂ)) * H j x)) := by
  obtain ⟨Ga, hGa, hfa⟩ := hga
  obtain ⟨Gb, hGb, hfb⟩ := hgb
  rw [physicalH1Graph_gradient_unique volume (Or.inl rfl) f Ga G hGa hG] at hfa
  rw [physicalH1Graph_gradient_unique volume (Or.inl rfl) f Gb G hGb hG] at hfb
  have hp (c : Vec d → Mat d)
      (hc : ∀ j k, MemLp (fun x => (c x j k : ℂ)) ∞ volume) :
      Integrable (fun x => ∑ j, ∑ k, (c x k j : ℂ) * G k x * H j x) volume := by
    apply integrable_finsetSum
    intro j _
    apply integrable_finsetSum
    intro k _
    exact ((hc k j).mul (r := 2) (Lp.memLp (G k))).integrable_mul (Lp.memLp (H j))
  have hd (c : Vec d → Mat d)
      (hc : ∀ j k, MemLp (fun x => (c x j k : ℂ)) ∞ volume) :
      Integrable (fun x => f x * (∑ j, (c x j i : ℂ) * H j x)) volume := by
    have : Integrable (fun x => ∑ j, (c x j i : ℂ) * H j x * f x) volume := by
      apply integrable_finsetSum
      intro j _
      exact ((hc j i).mul (r := 2) (Lp.memLp (H j))).integrable_mul (Lp.memLp f)
    simpa only [Finset.sum_mul, Finset.mul_sum, mul_comm] using this
  rw [hfa v H hH, hfb v H hH]
  have he1 : (fun x => ∑ j, ∑ k, ((a x k j : ℂ) - (b x k j : ℂ)) * G k x * H j x) =
      (fun x => (∑ j, ∑ k, (a x k j : ℂ) * G k x * H j x) -
        (∑ j, ∑ k, (b x k j : ℂ) * G k x * H j x)) := by
    funext x
    simp only [sub_mul, Finset.sum_sub_distrib]
  have he2 : (fun x => f x * (∑ j, ((a x j i : ℂ) - (b x j i : ℂ)) * H j x)) =
      (fun x => f x * (∑ j, (a x j i : ℂ) * H j x) -
        f x * (∑ j, (b x j i : ℂ) * H j x)) := by
    funext x
    simp only [sub_mul, Finset.sum_sub_distrib, mul_sub]
  rw [he1, he2, integral_sub (hp a ha) (hp b hb), integral_sub (hd a ha) (hd b hb)]
  ring

/-- The bilinear physical mass pairing used in the comparison of two evolutions. -/
noncomputable def s4PhysicalMassPairing {d : ℕ} :
    Lp ℂ 2 (volume : Measure (Vec d)) →L[ℝ]
      Lp ℂ 2 (volume : Measure (Vec d)) →L[ℝ] ℂ :=
  ((ContinuousLinearMap.mul ℂ ℂ).lpPairing volume 2 2).bilinearRestrictScalars ℝ

/-- Time-averaged physical orbits obey the forward/backward bilinear product rule. -/
theorem s4_physical_averaged_orbits_pairing_deriv {d : ℕ}
    {a b : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    {P R T : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (hP : IsPhysicalComplexSemigroup a i ζ P)
    (hT : IsPhysicalComplexTransposeSemigroup b i ζ R T)
    (f v : Lp ℂ 2 (volume : Measure (Vec d))) (ε δ : ℝ≥0) (S t : ℝ)
    (ht : 0 < t) (htS : t < S) :
    let fε := ((ε : ℝ) : ℂ)⁻¹ • ∫ s in (0 : ℝ)..(ε : ℝ), P s.toNNReal f
    let gε := ((ε : ℝ) : ℂ)⁻¹ • (P ε f - f)
    let vδ := ((δ : ℝ) : ℂ)⁻¹ • ∫ s in (0 : ℝ)..(δ : ℝ), T s.toNNReal v
    let wδ := ((δ : ℝ) : ℂ)⁻¹ • (T δ v - v)
    HasDerivAt (fun s : ℝ => s4PhysicalMassPairing (P s.toNNReal fε)
      (T (S - s).toNNReal vδ))
      (s4PhysicalMassPairing (P t.toNNReal gε) (T (S - t).toNNReal vδ) -
       s4PhysicalMassPairing (P t.toNNReal fε) (T (S - t).toNNReal wδ)) t := by
  dsimp only
  have hp := (Blueprint.crudeEnergy_physical_forward_averaged_orbit hP f ε).2.2.1 t ht
  have hq := ((Blueprint.crudeEnergy_physical_transpose_averaged_orbit hT v δ).2.2.1
    (S - t) (sub_pos.mpr htS)).scomp t ((hasDerivAt_id t).const_sub S)
  have hh := s4PhysicalMassPairing.hasDerivAt_of_bilinear (fun _ => hp) (fun _ => hq)
  simpa only [Function.comp_apply, zero_sub, neg_smul, one_smul, map_neg,
    sub_eq_add_neg, add_comm] using! hh


/-- Forward and transpose graphs for different fields have a bilinear defect
consisting exactly of the difference of their coefficients. -/
theorem s4_physical_mixed_generator_coefficient_difference {d : ℕ}
    (a b : Vec d → Mat d) (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (hb : ∀ j k, MemLp (fun x => (b x j k : ℂ)) ∞ volume)
    (f Af v Bv : Lp ℂ 2 (volume : Measure (Vec d)))
    (G H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    (hH : IsPhysicalH1Graph volume (Or.inl rfl) v H)
    (hf : IsPhysicalComplexGeneratorPair a i ζ f Af)
    (hv : IsPhysicalComplexTransposeGeneratorPair b i ζ v Bv) :
    (∫ x, Af x * v x) - (∫ x, f x * Bv x) =
      -(1 / 2 : ℂ) * (∫ x, ∑ j, ∑ k,
        ((a x j k : ℂ) - (b x j k : ℂ)) * G k x * H j x) +
      ζ * (∫ x, (∑ j, ((a x j i : ℂ) - (b x j i : ℂ)) * G j x) * v x) := by
  obtain ⟨Gf, hGf, hf⟩ := hf
  obtain ⟨Hv, hHv, hv⟩ := hv
  rw [physicalH1Graph_gradient_unique volume (Or.inl rfl) f Gf G hGf hG] at hf
  rw [physicalH1Graph_gradient_unique volume (Or.inl rfl) v Hv H hHv hH] at hv
  have hp (c : Vec d → Mat d)
      (hc : ∀ j k, MemLp (fun x => (c x j k : ℂ)) ∞ volume) :
      Integrable (fun x => ∑ j, ∑ k, (c x j k : ℂ) * G k x * H j x) volume := by
    apply integrable_finsetSum
    intro j _
    apply integrable_finsetSum
    intro k _
    exact ((hc j k).mul (r := 2) (Lp.memLp (G k))).integrable_mul (Lp.memLp (H j))
  have hd (c : Vec d → Mat d)
      (hc : ∀ j k, MemLp (fun x => (c x j k : ℂ)) ∞ volume) :
      Integrable (fun x => (∑ j, (c x j i : ℂ) * G j x) * v x) volume := by
    have : Integrable (fun x => ∑ j, (c x j i : ℂ) * G j x * v x) volume := by
      apply integrable_finsetSum
      intro j _
      exact ((hc j i).mul (r := 2) (Lp.memLp (G j))).integrable_mul (Lp.memLp v)
    simpa only [Finset.sum_mul] using this
  have hswap : (∫ x, f x * Bv x) = ∫ x, Bv x * f x := by
    congr 1
    ext x
    exact mul_comm _ _
  have hprincipal : (fun x => ∑ j, ∑ k, (b x k j : ℂ) * H k x * G j x) =
      (fun x => ∑ j, ∑ k, (b x j k : ℂ) * G k x * H j x) := by
    funext x
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hdrift : (fun x => v x * (∑ j, (b x j i : ℂ) * G j x)) =
      (fun x => (∑ j, (b x j i : ℂ) * G j x) * v x) := by
    funext x
    exact mul_comm _ _
  have he1 : (fun x => ∑ j, ∑ k, ((a x j k : ℂ) - (b x j k : ℂ)) * G k x * H j x) =
      (fun x => (∑ j, ∑ k, (a x j k : ℂ) * G k x * H j x) -
        (∑ j, ∑ k, (b x j k : ℂ) * G k x * H j x)) := by
    funext x
    simp only [sub_mul, Finset.sum_sub_distrib]
  have he2 : (fun x => (∑ j, ((a x j i : ℂ) - (b x j i : ℂ)) * G j x) * v x) =
      (fun x => (∑ j, (a x j i : ℂ) * G j x) * v x -
        (∑ j, (b x j i : ℂ) * G j x) * v x) := by
    funext x
    simp only [sub_mul, Finset.sum_sub_distrib]
  rw [hswap, hf v H hH, hv f G hG, hprincipal, hdrift, he1, he2,
    integral_sub (hp a ha) (hp b hb), integral_sub (hd a ha) (hd b hb)]
  ring


/-- The actual averaged forward/backward orbits satisfy an integrated
Duhamel identity, including the endpoints. -/
theorem s4_physical_averaged_orbits_duhamel {d : ℕ}
    {a b : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    {P R T : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (hP : IsPhysicalComplexSemigroup a i ζ P)
    (hT : IsPhysicalComplexTransposeSemigroup b i ζ R T)
    (f v : Lp ℂ 2 (volume : Measure (Vec d))) (ε δ : ℝ≥0) (S : ℝ) (hS : 0 < S) :
    let fε := ((ε : ℝ) : ℂ)⁻¹ • ∫ s in (0 : ℝ)..(ε : ℝ), P s.toNNReal f
    let gε := ((ε : ℝ) : ℂ)⁻¹ • (P ε f - f)
    let vδ := ((δ : ℝ) : ℂ)⁻¹ • ∫ s in (0 : ℝ)..(δ : ℝ), T s.toNNReal v
    let wδ := ((δ : ℝ) : ℂ)⁻¹ • (T δ v - v)
    (∫ s in (0 : ℝ)..S,
      s4PhysicalMassPairing (P s.toNNReal gε) (T (S - s).toNNReal vδ) -
      s4PhysicalMassPairing (P s.toNNReal fε) (T (S - s).toNNReal wδ)) =
      s4PhysicalMassPairing (P S.toNNReal fε) vδ -
      s4PhysicalMassPairing fε (T S.toNNReal vδ) := by
  dsimp only
  let fε := ((ε : ℝ) : ℂ)⁻¹ • ∫ s in (0 : ℝ)..(ε : ℝ), P s.toNNReal f
  let gε := ((ε : ℝ) : ℂ)⁻¹ • (P ε f - f)
  let vδ := ((δ : ℝ) : ℂ)⁻¹ • ∫ s in (0 : ℝ)..(δ : ℝ), T s.toNNReal v
  let wδ := ((δ : ℝ) : ℂ)⁻¹ • (T δ v - v)
  have hf : Continuous (fun s : ℝ => P s.toNNReal fε) :=
    (hP.2.2.1 fε).comp continuous_real_toNNReal
  have hg : Continuous (fun s : ℝ => P s.toNNReal gε) :=
    (hP.2.2.1 gε).comp continuous_real_toNNReal
  have hv : Continuous (fun s : ℝ => T (S - s).toNNReal vδ) :=
    ((hT.2.2.1 vδ).comp continuous_real_toNNReal).comp (continuous_const.sub continuous_id)
  have hw : Continuous (fun s : ℝ => T (S - s).toNNReal wδ) :=
    ((hT.2.2.1 wδ).comp continuous_real_toNNReal).comp (continuous_const.sub continuous_id)
  have hpair : Continuous (fun s : ℝ => s4PhysicalMassPairing
      (P s.toNNReal fε) (T (S - s).toNNReal vδ)) :=
    (s4PhysicalMassPairing.continuous.comp hf).clm_apply hv
  have hder : Continuous (fun s : ℝ =>
      s4PhysicalMassPairing (P s.toNNReal gε) (T (S - s).toNNReal vδ) -
      s4PhysicalMassPairing (P s.toNNReal fε) (T (S - s).toNNReal wδ)) :=
    ((s4PhysicalMassPairing.continuous.comp hg).clm_apply hv).sub
      ((s4PhysicalMassPairing.continuous.comp hf).clm_apply hw)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hS
    (fun t ht => s4_physical_averaged_orbits_pairing_deriv hP hT f v ε δ S t ht.1 ht.2)
    (hder.intervalIntegrable 0 S)
    (hpair.continuousAt.mono_left nhdsWithin_le_nhds)
    (hpair.continuousAt.mono_left nhdsWithin_le_nhds)
  simpa only [sub_self, Real.toNNReal_zero, hP.1, hT.1,
    ContinuousLinearMap.id_apply, sub_zero] using hFTC


/-- The averaged-orbit Duhamel derivative is the actual coefficient defect,
with the gradients supplied by the two weak generator graphs. -/
theorem s4_physical_averaged_orbits_coefficient_deriv {d : ℕ}
    {a b : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    {P R T : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (hb : ∀ j k, MemLp (fun x => (b x j k : ℂ)) ∞ volume)
    (hP : IsPhysicalComplexSemigroup a i ζ P)
    (hT : IsPhysicalComplexTransposeSemigroup b i ζ R T)
    (f v : Lp ℂ 2 (volume : Measure (Vec d))) (ε δ : ℝ≥0) (S t : ℝ)
    (ht : 0 < t) (htS : t < S) :
    let fε := ((ε : ℝ) : ℂ)⁻¹ • ∫ s in (0 : ℝ)..(ε : ℝ), P s.toNNReal f
    let vδ := ((δ : ℝ) : ℂ)⁻¹ • ∫ s in (0 : ℝ)..(δ : ℝ), T s.toNNReal v
    ∃ (G H : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) (P t.toNNReal fε) G ∧
      IsPhysicalH1Graph volume (Or.inl rfl) (T (S - t).toNNReal vδ) H ∧
      HasDerivAt (fun s : ℝ => s4PhysicalMassPairing (P s.toNNReal fε)
          (T (S - s).toNNReal vδ))
        (-(1 / 2 : ℂ) * (∫ x, ∑ j, ∑ k,
          ((a x j k : ℂ) - (b x j k : ℂ)) * G k x * H j x) +
          ζ * (∫ x, (∑ j, ((a x j i : ℂ) - (b x j i : ℂ)) * G j x) *
            (T (S - t).toNNReal vδ) x)) t := by
  dsimp only
  have hf := (Blueprint.crudeEnergy_physical_forward_averaged_orbit hP f ε).2.2.2 t.toNNReal
  have hv := (Blueprint.crudeEnergy_physical_transpose_averaged_orbit hT v δ).2.2.2
    (S - t).toNNReal
  obtain ⟨G, hG, hfg⟩ := hf
  obtain ⟨H, hH, hvh⟩ := hv
  refine ⟨G, H, hG, hH, ?_⟩
  have he := s4_physical_mixed_generator_coefficient_difference a b i ζ ha hb _ _ _ _
    G H hG hH ⟨G, hG, hfg⟩ ⟨H, hH, hvh⟩
  have hp := s4_physical_averaged_orbits_pairing_deriv hP hT f v ε δ S t ht htS
  have hpair (u w : Lp ℂ 2 (volume : Measure (Vec d))) :
      s4PhysicalMassPairing u w = ∫ x, u x * w x := by
    exact (ContinuousLinearMap.mul ℂ ℂ).lpPairing_eq_integral u w
  convert hp using 1
  simpa only [hpair] using he.symm



/-- A time average of a strongly continuous physical evolution. -/
noncomputable def s4PhysicalTimeAverage {d : ℕ}
    (P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (f : Lp ℂ 2 (volume : Measure (Vec d))) (ε : ℝ≥0) :
    Lp ℂ 2 (volume : Measure (Vec d)) :=
  ((ε : ℝ) : ℂ)⁻¹ • ∫ s in (0 : ℝ)..(ε : ℝ), P s.toNNReal f

/-- Applying a fixed evolution time to its averages preserves their initial limit. -/
theorem s4_physical_time_average_tendsto {d : ℕ}
    {P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (hP0 : P 0 = ContinuousLinearMap.id ℂ _)
    (hPc : ∀ f, Continuous (fun t => P t f))
    (f : Lp ℂ 2 (volume : Measure (Vec d))) (t : ℝ≥0) :
    Tendsto (fun ε => P t (s4PhysicalTimeAverage P f ε))
      (𝓝[>] (0 : ℝ≥0)) (𝓝 (P t f)) := by
  exact Blueprint.crudeEnergy_complex_time_average_tendsto hP0 hPc f t

/-- Small positive time averages have norm at most twice that of the datum. -/
theorem s4_physical_time_average_eventually_norm_le {d : ℕ}
    {P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (hP0 : P 0 = ContinuousLinearMap.id ℂ _)
    (hPc : ∀ f, Continuous (fun t => P t f))
    (f : Lp ℂ 2 (volume : Measure (Vec d))) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ≥0), ‖s4PhysicalTimeAverage P f ε‖ ≤ 2 * ‖f‖ := by
  by_cases hf : f = 0
  · subst f
    filter_upwards [] with ε
    simp [s4PhysicalTimeAverage]
  · have hnorm : 0 < ‖f‖ := norm_pos_iff.mpr hf
    have hlim := (s4_physical_time_average_tendsto hP0 hPc f 0).norm
    simp only [hP0, ContinuousLinearMap.id_apply] at hlim
    have hevent := hlim.eventually (Iio_mem_nhds (show ‖f‖ < 2 * ‖f‖ by linarith))
    filter_upwards [hevent] with ε hε
    exact le_of_lt hε

/-- A continuous bilinear map preserves simultaneous filter limits. -/
theorem s4_bilinear_tendsto {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {α : Type*} {l : Filter α} (B : E →L[ℝ] F →L[ℝ] G)
    {f : α → E} {v : α → F} {f₀ : E} {v₀ : F}
    (hf : Tendsto f l (𝓝 f₀)) (hv : Tendsto v l (𝓝 v₀)) :
    Tendsto (fun t => B (f t) (v t)) l (𝓝 (B f₀ v₀)) := by
  exact (B.continuous₂.tendsto (f₀, v₀)).comp (hf.prodMk_nhds hv)

/-- Averaged Duhamel endpoints converge to those for the original data. -/
theorem s4_physical_averaged_orbits_endpoints_tendsto {d : ℕ}
    {a b : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    {P R T : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (hP : IsPhysicalComplexSemigroup a i ζ P)
    (hT : IsPhysicalComplexTransposeSemigroup b i ζ R T)
    (f v : Lp ℂ 2 (volume : Measure (Vec d))) (S : ℝ≥0) :
    Tendsto (fun ε =>
      s4PhysicalMassPairing (P S (s4PhysicalTimeAverage P f ε))
          (s4PhysicalTimeAverage T v ε) -
      s4PhysicalMassPairing (s4PhysicalTimeAverage P f ε)
          (T S (s4PhysicalTimeAverage T v ε)))
      (𝓝[>] (0 : ℝ≥0))
      (𝓝 (s4PhysicalMassPairing (P S f) v - s4PhysicalMassPairing f (T S v))) := by
  have hf : Tendsto (s4PhysicalTimeAverage P f) (𝓝[>] (0 : ℝ≥0)) (𝓝 f) := by
    simpa only [hP.1, ContinuousLinearMap.id_apply] using
      s4_physical_time_average_tendsto hP.1 hP.2.2.1 f 0
  have hv : Tendsto (s4PhysicalTimeAverage T v) (𝓝[>] (0 : ℝ≥0)) (𝓝 v) := by
    simpa only [hT.1, ContinuousLinearMap.id_apply] using
      s4_physical_time_average_tendsto hT.1 hT.2.2.1 v 0
  exact (s4_bilinear_tendsto s4PhysicalMassPairing
    (s4_physical_time_average_tendsto hP.1 hP.2.2.1 f S) hv).sub
    (s4_bilinear_tendsto s4PhysicalMassPairing hf
      (s4_physical_time_average_tendsto hT.1 hT.2.2.1 v S))


/-- The integrated generator defect of averaged actual orbits converges to the
Duhamel endpoint difference for the original data. -/
theorem s4_physical_averaged_orbits_duhamel_tendsto {d : ℕ}
    {a b : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    {P R T : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (hP : IsPhysicalComplexSemigroup a i ζ P)
    (hT : IsPhysicalComplexTransposeSemigroup b i ζ R T)
    (f v : Lp ℂ 2 (volume : Measure (Vec d))) (S : ℝ) (hS : 0 < S) :
    Tendsto (fun ε : ℝ≥0 =>
      let fε := s4PhysicalTimeAverage P f ε
      let gε := ((ε : ℝ) : ℂ)⁻¹ • (P ε f - f)
      let vε := s4PhysicalTimeAverage T v ε
      let wε := ((ε : ℝ) : ℂ)⁻¹ • (T ε v - v)
      ∫ s in (0 : ℝ)..S,
        s4PhysicalMassPairing (P s.toNNReal gε) (T (S - s).toNNReal vε) -
        s4PhysicalMassPairing (P s.toNNReal fε) (T (S - s).toNNReal wε))
      (𝓝[>] (0 : ℝ≥0))
      (𝓝 (s4PhysicalMassPairing (P S.toNNReal f) v -
        s4PhysicalMassPairing f (T S.toNNReal v))) := by
  apply Filter.Tendsto.congr ?_
    (s4_physical_averaged_orbits_endpoints_tendsto hP hT f v S.toNNReal)
  intro ε
  symm
  exact s4_physical_averaged_orbits_duhamel hP hT f v ε ε S hS

/-- An integrand vanishing on a measurable set is supported on its complement. -/
theorem s4_integral_eq_compl_of_zero_on {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (A : Set α) (hA : MeasurableSet A)
    (g : α → ℂ) (hg : ∀ x ∈ A, g x = 0) :
    (∫ x, g x ∂μ) = ∫ x in Aᶜ, g x ∂μ := by
  rw [← integral_indicator hA.compl]
  congr 1
  funext x
  by_cases hx : x ∈ A
  · simp [Set.indicator, hx, hg x hx]
  · simp [Set.indicator, hx]

/-- The averaged-orbit coefficient defect is supported outside any measurable
region on which the two physical coefficient fields agree. -/
theorem s4_physical_averaged_orbits_localized_coefficient_deriv {d : ℕ}
    {a b : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    {P R T : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (hb : ∀ j k, MemLp (fun x => (b x j k : ℂ)) ∞ volume)
    (hP : IsPhysicalComplexSemigroup a i ζ P)
    (hT : IsPhysicalComplexTransposeSemigroup b i ζ R T)
    (A : Set (Vec d)) (hA : MeasurableSet A) (hab : ∀ x ∈ A, a x = b x)
    (f v : Lp ℂ 2 (volume : Measure (Vec d))) (ε δ : ℝ≥0) (S t : ℝ)
    (ht : 0 < t) (htS : t < S) :
    let fε := ((ε : ℝ) : ℂ)⁻¹ • ∫ s in (0 : ℝ)..(ε : ℝ), P s.toNNReal f
    let vδ := ((δ : ℝ) : ℂ)⁻¹ • ∫ s in (0 : ℝ)..(δ : ℝ), T s.toNNReal v
    ∃ (G H : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) (P t.toNNReal fε) G ∧
      IsPhysicalH1Graph volume (Or.inl rfl) (T (S - t).toNNReal vδ) H ∧
      HasDerivAt (fun s : ℝ => s4PhysicalMassPairing (P s.toNNReal fε)
          (T (S - s).toNNReal vδ))
        (-(1 / 2 : ℂ) * (∫ x in Aᶜ, ∑ j, ∑ k,
          ((a x j k : ℂ) - (b x j k : ℂ)) * G k x * H j x) +
          ζ * (∫ x in Aᶜ, (∑ j, ((a x j i : ℂ) - (b x j i : ℂ)) * G j x) *
            (T (S - t).toNNReal vδ) x)) t := by
  obtain ⟨G, H, hG, hH, hd⟩ :=
    s4_physical_averaged_orbits_coefficient_deriv ha hb hP hT f v ε δ S t ht htS
  refine ⟨G, H, hG, hH, ?_⟩
  have hp := s4_integral_eq_compl_of_zero_on volume A hA
    (fun x => ∑ j, ∑ k, ((a x j k : ℂ) - (b x j k : ℂ)) * G k x * H j x)
    (by intro x hx; simp [hab x hx])
  have hf := s4_integral_eq_compl_of_zero_on volume A hA
    (fun x => (∑ j, ((a x j i : ℂ) - (b x j i : ℂ)) * G j x) *
      (T (S - t).toNNReal (((δ : ℝ) : ℂ)⁻¹ •
        ∫ s in (0 : ℝ)..(δ : ℝ), T s.toNNReal v)) x)
    (by intro x hx; simp [hab x hx])
  rw [hp, hf] at hd
  exact hd

/-- A continuous Duhamel integrand, represented on the interior by the
actual coefficient defect outside the coefficient-agreement region. -/
theorem s4_physical_localized_averaged_duhamel {d : ℕ}
    {a b : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    {P R T : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (hb : ∀ j k, MemLp (fun x => (b x j k : ℂ)) ∞ volume)
    (hP : IsPhysicalComplexSemigroup a i ζ P)
    (hT : IsPhysicalComplexTransposeSemigroup b i ζ R T)
    (A : Set (Vec d)) (hA : MeasurableSet A) (hab : ∀ x ∈ A, a x = b x)
    (f v : Lp ℂ 2 (volume : Measure (Vec d))) (ε δ : ℝ≥0) (S : ℝ)
    (hS : 0 < S) :
    let fε := ((ε : ℝ) : ℂ)⁻¹ • ∫ s in (0 : ℝ)..(ε : ℝ), P s.toNNReal f
    let vδ := ((δ : ℝ) : ℂ)⁻¹ • ∫ s in (0 : ℝ)..(δ : ℝ), T s.toNNReal v
    ∃ D : ℝ → ℂ, Continuous D ∧
      (∀ t, 0 < t → t < S →
        ∃ G H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
          IsPhysicalH1Graph volume (Or.inl rfl) (P t.toNNReal fε) G ∧
          IsPhysicalH1Graph volume (Or.inl rfl) (T (S - t).toNNReal vδ) H ∧
          D t = -(1 / 2 : ℂ) * (∫ x in Aᶜ, ∑ j, ∑ k,
            ((a x j k : ℂ) - (b x j k : ℂ)) * G k x * H j x) +
            ζ * (∫ x in Aᶜ, (∑ j, ((a x j i : ℂ) - (b x j i : ℂ)) * G j x) *
              (T (S - t).toNNReal vδ) x)) ∧
      (∫ t in (0 : ℝ)..S, D t) =
        s4PhysicalMassPairing (P S.toNNReal fε) vδ -
        s4PhysicalMassPairing fε (T S.toNNReal vδ) := by
  dsimp only
  let fε := ((ε : ℝ) : ℂ)⁻¹ • ∫ s in (0 : ℝ)..(ε : ℝ), P s.toNNReal f
  let gε := ((ε : ℝ) : ℂ)⁻¹ • (P ε f - f)
  let vδ := ((δ : ℝ) : ℂ)⁻¹ • ∫ s in (0 : ℝ)..(δ : ℝ), T s.toNNReal v
  let wδ := ((δ : ℝ) : ℂ)⁻¹ • (T δ v - v)
  let D := fun s : ℝ => s4PhysicalMassPairing (P s.toNNReal gε)
      (T (S - s).toNNReal vδ) -
    s4PhysicalMassPairing (P s.toNNReal fε) (T (S - s).toNNReal wδ)
  have hf : Continuous (fun s : ℝ => P s.toNNReal fε) :=
    (hP.2.2.1 fε).comp continuous_real_toNNReal
  have hg : Continuous (fun s : ℝ => P s.toNNReal gε) :=
    (hP.2.2.1 gε).comp continuous_real_toNNReal
  have hv : Continuous (fun s : ℝ => T (S - s).toNNReal vδ) :=
    ((hT.2.2.1 vδ).comp continuous_real_toNNReal).comp (continuous_const.sub continuous_id)
  have hw : Continuous (fun s : ℝ => T (S - s).toNNReal wδ) :=
    ((hT.2.2.1 wδ).comp continuous_real_toNNReal).comp (continuous_const.sub continuous_id)
  refine ⟨D, ((s4PhysicalMassPairing.continuous.comp hg).clm_apply hv).sub
    ((s4PhysicalMassPairing.continuous.comp hf).clm_apply hw), ?_, ?_⟩
  · intro t ht htS
    obtain ⟨G, H, hG, hH, hloc⟩ :=
      s4_physical_averaged_orbits_localized_coefficient_deriv ha hb hP hT A hA hab
        f v ε δ S t ht htS
    refine ⟨G, H, hG, hH, ?_⟩
    exact (s4_physical_averaged_orbits_pairing_deriv hP hT f v ε δ S t ht htS).unique hloc
  · exact s4_physical_averaged_orbits_duhamel hP hT f v ε δ S hS

/-- The localized averaged defects integrate to the unaveraged endpoint
difference in the limit as the averaging time tends to zero. -/
theorem s4_physical_localized_duhamel_averaging_limit {d : ℕ}
    {a b : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    {P R T : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (hb : ∀ j k, MemLp (fun x => (b x j k : ℂ)) ∞ volume)
    (hP : IsPhysicalComplexSemigroup a i ζ P)
    (hT : IsPhysicalComplexTransposeSemigroup b i ζ R T)
    (A : Set (Vec d)) (hA : MeasurableSet A) (hab : ∀ x ∈ A, a x = b x)
    (f v : Lp ℂ 2 (volume : Measure (Vec d))) (S : ℝ) (hS : 0 < S) :
    ∃ D : ℝ≥0 → ℝ → ℂ,
      (∀ ε, Continuous (D ε)) ∧
      (∀ ε t, 0 < t → t < S →
        ∃ G H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
          IsPhysicalH1Graph volume (Or.inl rfl)
            (P t.toNNReal (s4PhysicalTimeAverage P f ε)) G ∧
          IsPhysicalH1Graph volume (Or.inl rfl)
            (T (S-t).toNNReal (s4PhysicalTimeAverage T v ε)) H ∧
          D ε t = -(1 / 2 : ℂ) * (∫ x in Aᶜ, ∑ j, ∑ k,
            ((a x j k : ℂ) - (b x j k : ℂ)) * G k x * H j x) +
            ζ * (∫ x in Aᶜ, (∑ j, ((a x j i : ℂ) - (b x j i : ℂ)) * G j x) *
              (T (S-t).toNNReal (s4PhysicalTimeAverage T v ε)) x)) ∧
      Tendsto (fun ε => ∫ t in (0 : ℝ)..S, D ε t) (𝓝[>] (0 : ℝ≥0))
        (𝓝 (s4PhysicalMassPairing (P S.toNNReal f) v -
          s4PhysicalMassPairing f (T S.toNNReal v))) := by
  classical
  have hex : ∀ ε : ℝ≥0, ∃ D : ℝ → ℂ, Continuous D ∧
      (∀ t, 0 < t → t < S →
        ∃ G H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
          IsPhysicalH1Graph volume (Or.inl rfl)
            (P t.toNNReal (s4PhysicalTimeAverage P f ε)) G ∧
          IsPhysicalH1Graph volume (Or.inl rfl)
            (T (S-t).toNNReal (s4PhysicalTimeAverage T v ε)) H ∧
          D t = -(1 / 2 : ℂ) * (∫ x in Aᶜ, ∑ j, ∑ k,
            ((a x j k : ℂ) - (b x j k : ℂ)) * G k x * H j x) +
            ζ * (∫ x in Aᶜ, (∑ j, ((a x j i : ℂ) - (b x j i : ℂ)) * G j x) *
              (T (S-t).toNNReal (s4PhysicalTimeAverage T v ε)) x)) ∧
      (∫ t in (0 : ℝ)..S, D t) =
        s4PhysicalMassPairing (P S.toNNReal (s4PhysicalTimeAverage P f ε))
          (s4PhysicalTimeAverage T v ε) -
        s4PhysicalMassPairing (s4PhysicalTimeAverage P f ε)
          (T S.toNNReal (s4PhysicalTimeAverage T v ε)) := by
    intro ε
    exact s4_physical_localized_averaged_duhamel ha hb hP hT A hA hab f v ε ε S hS
  choose D hD using hex
  refine ⟨D, (fun ε => (hD ε).1), (fun ε => (hD ε).2.1), ?_⟩
  apply Filter.Tendsto.congr ?_
    (s4_physical_averaged_orbits_endpoints_tendsto hP hT f v S.toNNReal)
  intro ε
  exact ((hD ε).2.2).symm

/-- The actual averaged forward orbit has a continuous weak gradient. -/
theorem s4_physical_averaged_forward_continuous_gradient {d : ℕ}
    {a : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hell : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (hP : IsPhysicalComplexSemigroup a i ζ P)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) (ε : ℝ≥0) :
    ∃ G : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ t, IsPhysicalH1Graph volume (Or.inl rfl)
        (P t.toNNReal (s4PhysicalTimeAverage P f ε)) (G t)) ∧
      ∀ j, Continuous (fun t => G t j) := by
  have h := EinsteinFull.Blueprint.crudeEnergy_physical_forward_averaged_orbit hP f ε
  exact EinsteinFull.Blueprint.physical_generator_orbit_continuous_gradient a i ζ ha hΛ hell
    _ _ h.1 h.2.1 (fun t => h.2.2.2 t.toNNReal)

/-- The literal coefficient-defect flux of an averaged orbit is continuous in
L² and vanishes on every region where the coefficients agree. -/
theorem s4_physical_averaged_defect_flux {d : ℕ}
    {a b : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ B : ℝ} (hΛ : 0 < Λ) (hell : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (hB : 0 ≤ B)
    (hm : ∀ j k, Measurable (fun x => a x j k - b x j k))
    (hb : ∀ j k x, |a x j k - b x j k| ≤ B)
    (hP : IsPhysicalComplexSemigroup a i ζ P)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) (ε : ℝ≥0)
    (A : Set (Vec d)) (hab : ∀ x ∈ A, a x = b x) :
    ∃ G F : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ t, IsPhysicalH1Graph volume (Or.inl rfl)
        (P t.toNNReal (s4PhysicalTimeAverage P f ε)) (G t)) ∧
      (∀ j, Continuous (fun t => G t j)) ∧
      (∀ j, Continuous (fun t => F t j)) ∧
      (∀ t j, ∀ᵐ x ∂volume, F t j x = ∑ k,
        ((a x j k - b x j k : ℝ) : ℂ) * G t k x) ∧
      ∀ t j, ∀ᵐ x ∂volume, x ∈ A → F t j x = 0 := by
  classical
  obtain ⟨G, hG, hGc⟩ := s4_physical_averaged_forward_continuous_gradient
    ha hΛ hell hP f ε
  let F : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)) := fun t j =>
    ∑ k, s5Mul volume (hm j k) hB (hb j k) (G t k)
  refine ⟨G, F, hG, hGc, ?_, ?_, ?_⟩
  · intro j
    exact continuous_finset_sum Finset.univ fun k _ =>
      (s5Mul volume (hm j k) hB (hb j k)).continuous.comp (hGc k)
  · intro t j
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
        (fun k => s5Mul volume (hm j k) hB (hb j k) (G t k)),
      ae_all_iff.mpr (fun k => s5Mul_coe volume (hm j k) hB (hb j k) (G t k))]
      with x hs hm'
    change (∑ k, s5Mul volume (hm j k) hB (hb j k) (G t k)) x = _
    rw [hs]
    exact Finset.sum_congr rfl (fun k _ => hm' k)
  · intro t j
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
        (fun k => s5Mul volume (hm j k) hB (hb j k) (G t k)),
      ae_all_iff.mpr (fun k => s5Mul_coe volume (hm j k) hB (hb j k) (G t k))]
      with x hs hm' hx
    change (∑ k, s5Mul volume (hm j k) hB (hb j k) (G t k)) x = 0
    rw [hs]
    simp only [hm', hab x hx, sub_self, Complex.ofReal_zero, zero_mul, Finset.sum_const_zero]


/-- The force-column defect of an averaged orbit is continuous in L² and
vanishes where the coefficients agree. -/
theorem s4_physical_averaged_defect_column {d : ℕ}
    {a b : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ B : ℝ} (hΛ : 0 < Λ) (hell : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (hB : 0 ≤ B)
    (hm : ∀ j k, Measurable (fun x => a x j k - b x j k))
    (hb : ∀ j k x, |a x j k - b x j k| ≤ B)
    (hP : IsPhysicalComplexSemigroup a i ζ P)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) (ε : ℝ≥0)
    (A : Set (Vec d)) (hab : ∀ x ∈ A, a x = b x) :
    ∃ G : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
    ∃ Q : ℝ → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ t, IsPhysicalH1Graph volume (Or.inl rfl)
        (P t.toNNReal (s4PhysicalTimeAverage P f ε)) (G t)) ∧
      (∀ j, Continuous (fun t => G t j)) ∧ Continuous Q ∧
      (∀ t, ∀ᵐ x ∂volume, Q t x = ∑ j,
        ((a x j i - b x j i : ℝ) : ℂ) * G t j x) ∧
      ∀ t, ∀ᵐ x ∂volume, x ∈ A → Q t x = 0 := by
  classical
  obtain ⟨G, hG, hGc⟩ := s4_physical_averaged_forward_continuous_gradient
    ha hΛ hell hP f ε
  let Q : ℝ → Lp ℂ 2 (volume : Measure (Vec d)) := fun t =>
    ∑ j, s5Mul volume (hm j i) hB (hb j i) (G t j)
  refine ⟨G, Q, hG, hGc, ?_, ?_, ?_⟩
  · exact continuous_finset_sum Finset.univ fun j _ =>
      (s5Mul volume (hm j i) hB (hb j i)).continuous.comp (hGc j)
  · intro t
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
        (fun j => s5Mul volume (hm j i) hB (hb j i) (G t j)),
      ae_all_iff.mpr (fun j => s5Mul_coe volume (hm j i) hB (hb j i) (G t j))]
      with x hs hm'
    change (∑ j, s5Mul volume (hm j i) hB (hb j i) (G t j)) x = _
    rw [hs]
    exact Finset.sum_congr rfl (fun j _ => hm' j)
  · intro t
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
        (fun j => s5Mul volume (hm j i) hB (hb j i) (G t j)),
      ae_all_iff.mpr (fun j => s5Mul_coe volume (hm j i) hB (hb j i) (G t j))]
      with x hs hm' hx
    change (∑ j, s5Mul volume (hm j i) hB (hb j i) (G t j)) x = 0
    rw [hs]
    simp only [hm', hab x hx, sub_self, Complex.ofReal_zero, zero_mul, Finset.sum_const_zero]


/-- The vector flux and force-column defect can be chosen with the same
continuous averaged-orbit gradient. -/
theorem s4_physical_averaged_defects {d : ℕ}
    {a b : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ B : ℝ} (hΛ : 0 < Λ) (hell : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (hB : 0 ≤ B)
    (hm : ∀ j k, Measurable (fun x => a x j k - b x j k))
    (hb : ∀ j k x, |a x j k - b x j k| ≤ B)
    (hP : IsPhysicalComplexSemigroup a i ζ P)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) (ε : ℝ≥0)
    (A : Set (Vec d)) (hab : ∀ x ∈ A, a x = b x) :
    ∃ G F : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
    ∃ Q : ℝ → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ t, IsPhysicalH1Graph volume (Or.inl rfl)
        (P t.toNNReal (s4PhysicalTimeAverage P f ε)) (G t)) ∧
      (∀ j, Continuous (fun t => G t j)) ∧
      (∀ j, Continuous (fun t => F t j)) ∧ Continuous Q ∧
      (∀ t j, ∀ᵐ x ∂volume, F t j x = ∑ k,
        ((a x j k - b x j k : ℝ) : ℂ) * G t k x) ∧
      (∀ t, ∀ᵐ x ∂volume, Q t x = ∑ j,
        ((a x j i - b x j i : ℝ) : ℂ) * G t j x) ∧
      (∀ t j, ∀ᵐ x ∂volume, x ∈ A → F t j x = 0) ∧
      ∀ t, ∀ᵐ x ∂volume, x ∈ A → Q t x = 0 := by
  obtain ⟨G, F, hG, hGc, hFc, hF, hFs⟩ :=
    s4_physical_averaged_defect_flux ha hΛ hell hB hm hb hP f ε A hab
  obtain ⟨G', Q, hG', hGc', hQc, hQ, hQs⟩ :=
    s4_physical_averaged_defect_column ha hΛ hell hB hm hb hP f ε A hab
  have heq : G' = G := by
    funext t
    exact physicalH1Graph_gradient_unique volume (Or.inl rfl) _ _ _ (hG' t) (hG t)
  subst G'
  exact ⟨G, F, Q, hG, hGc, hFc, hQc, hF, hQ, hFs, hQs⟩


/-- A finite coefficient-defect sum is controlled by the L² gradient norms. -/
theorem s4_defect_multiplier_sum_norm_le {d : ℕ}
    (w : Fin d → Vec d → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hm : ∀ j, Measurable (w j)) (hb : ∀ j x, |w j x| ≤ B)
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :
    ‖∑ j, s5Mul volume (hm j) hB (hb j) (G j)‖ ≤
      B * ∑ j, ‖G j‖ := by
  have hmul : ∀ j, ‖s5Mul volume (hm j) hB (hb j) (G j)‖ ≤ B * ‖G j‖ := by
    intro j
    rw [s5Mul_norm volume (hm j) hB (hb j), Lp.norm_def]
    have h := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (μ := (volume : Measure (Vec d)))
      (f := fun x => (w j x : ℂ) * G j x) (g := (G j : Vec d → ℂ)) (c := B)
      ((Complex.measurable_ofReal.comp (hm j)).aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable (G j)))
      (Filter.Eventually.of_forall fun x => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hb j x) (norm_nonneg _)) 2
    calc
      _ ≤ (ENNReal.ofReal B * eLpNorm (G j : Vec d → ℂ) 2 volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (Lp.eLpNorm_ne_top (G j))) h
      _ = _ := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hB]
  calc
    ‖∑ j, s5Mul volume (hm j) hB (hb j) (G j)‖ ≤
        ∑ j, ‖s5Mul volume (hm j) hB (hb j) (G j)‖ := norm_sum_le _ _
    _ ≤ ∑ j, B * ‖G j‖ := Finset.sum_le_sum fun j _ => hmul j
    _ = B * ∑ j, ‖G j‖ := (Finset.mul_sum _ _ _).symm


/-- The coefficient-defect multiplier sum is controlled by the Euclidean
L² gradient energy. -/
theorem s4_defect_multiplier_sum_energy_le {d : ℕ}
    (w : Fin d → Vec d → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hm : ∀ j, Measurable (w j)) (hb : ∀ j x, |w j x| ≤ B)
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :
    ‖∑ j, s5Mul volume (hm j) hB (hb j) (G j)‖ ≤
      B * (Real.sqrt d * Real.sqrt (∑ j, ‖G j‖ ^ 2)) := by
  have hn : 0 ≤ ∑ j : Fin d, ‖G j‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
  have he : 0 ≤ ∑ j : Fin d, ‖G j‖ ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hsq := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j : Fin d => ‖G j‖)
  simp only [Finset.card_univ, Fintype.card_fin] at hsq
  have hd := Real.sq_sqrt (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  have hg := Real.sq_sqrt he
  have hr : 0 ≤ Real.sqrt d * Real.sqrt (∑ j, ‖G j‖ ^ 2) := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hprod : (Real.sqrt d * Real.sqrt (∑ j, ‖G j‖ ^ 2)) ^ 2 =
      (d : ℝ) * ∑ j, ‖G j‖ ^ 2 := by rw [mul_pow, hd, hg]
  have hsum : (∑ j : Fin d, ‖G j‖) ≤
      Real.sqrt d * Real.sqrt (∑ j : Fin d, ‖G j‖ ^ 2) := by
    nlinarith [sq_nonneg (Real.sqrt d * Real.sqrt (∑ j : Fin d, ‖G j‖ ^ 2) - ∑ j : Fin d, ‖G j‖)]
  exact (s4_defect_multiplier_sum_norm_le w hB hm hb G).trans
    (mul_le_mul_of_nonneg_left hsum hB)

/-- An almost-everywhere coefficient-defect representation inherits the
multiplier energy bound. -/
theorem s4_defect_ae_energy_le {d : ℕ}
    (w : Fin d → Vec d → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hm : ∀ j, Measurable (w j)) (hb : ∀ j x, |w j x| ≤ B)
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (F : Lp ℂ 2 (volume : Measure (Vec d)))
    (hF : ∀ᵐ x ∂volume, F x = ∑ j, ((w j x : ℝ) : ℂ) * G j x) :
    ‖F‖ ≤ B * (Real.sqrt d * Real.sqrt (∑ j, ‖G j‖ ^ 2)) := by
  have heq : F = ∑ j, s5Mul volume (hm j) hB (hb j) (G j) := by
    apply Lp.ext
    filter_upwards [hF, Lp.coeFn_fun_finsetSum Finset.univ
      (fun j => s5Mul volume (hm j) hB (hb j) (G j)),
      ae_all_iff.mpr (fun j => s5Mul_coe volume (hm j) hB (hb j) (G j))]
      with x hx hs hm'
    rw [hx, hs]
    exact Finset.sum_congr rfl (fun j _ => (hm' j).symm)
  rw [heq]
  exact s4_defect_multiplier_sum_energy_le w hB hm hb G

/-- Uniform component bounds control the Euclidean energy of a finite flux. -/
theorem s4_flux_energy_le_of_component_bound {d : ℕ}
    (F : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    {K : ℝ} (hK : 0 ≤ K) (hF : ∀ j, ‖F j‖ ≤ K) :
    Real.sqrt (∑ j, ‖F j‖ ^ 2) ≤ Real.sqrt d * K := by
  have he : 0 ≤ ∑ j : Fin d, ‖F j‖ ^ 2 :=
    Finset.sum_nonneg fun j _ => sq_nonneg _
  have hsq : (∑ j : Fin d, ‖F j‖ ^ 2) ≤ (d : ℝ) * K ^ 2 := by
    calc
      _ ≤ ∑ _j : Fin d, K ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        nlinarith [norm_nonneg (F j), hF j]
      _ = _ := by simp
  have hs := Real.sq_sqrt he
  have hd := Real.sq_sqrt (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  have hprod : (Real.sqrt d * K) ^ 2 = (d : ℝ) * K ^ 2 := by rw [mul_pow, hd]
  have hr := mul_nonneg (Real.sqrt_nonneg d) hK
  nlinarith [Real.sqrt_nonneg (∑ j : Fin d, ‖F j‖ ^ 2)]

/-- A matrix coefficient defect controls the full flux by the gradient energy. -/
theorem s4_defect_flux_energy_le {d : ℕ}
    (w : Fin d → Fin d → Vec d → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hm : ∀ j k, Measurable (w j k)) (hb : ∀ j k x, |w j k x| ≤ B)
    (G F : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hF : ∀ j, ∀ᵐ x ∂volume, F j x = ∑ k, ((w j k x : ℝ) : ℂ) * G k x) :
    Real.sqrt (∑ j, ‖F j‖ ^ 2) ≤
      (d : ℝ) * B * Real.sqrt (∑ j, ‖G j‖ ^ 2) := by
  have hK : 0 ≤ B * (Real.sqrt d * Real.sqrt (∑ j, ‖G j‖ ^ 2)) :=
    mul_nonneg hB (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hbound := s4_flux_energy_le_of_component_bound F hK
    (fun j => s4_defect_ae_energy_le (w j) hB (hm j) (hb j) G (F j) (hF j))
  have hd := Real.sq_sqrt (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  calc
    _ ≤ Real.sqrt d * (B * (Real.sqrt d * Real.sqrt (∑ j, ‖G j‖ ^ 2))) := hbound
    _ = (Real.sqrt d) ^ 2 * B * Real.sqrt (∑ j, ‖G j‖ ^ 2) := by ring
    _ = _ := by rw [hd]

/-- A singular gradient-energy bound transfers to the literal defect flux. -/
theorem s4_defect_flux_singular_le {d : ℕ}
    (w : Fin d → Fin d → Vec d → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hm : ∀ j k, Measurable (w j k)) (hb : ∀ j k x, |w j k x| ≤ B)
    (G F : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hF : ∀ j, ∀ᵐ x ∂volume, F j x = ∑ k, ((w j k x : ℝ) : ℂ) * G k x)
    {T K : ℝ}
    (hG : Real.sqrt (∑ j, ‖G j‖ ^ 2) ≤ (Real.sqrt T)⁻¹ * K) :
    Real.sqrt (∑ j, ‖F j‖ ^ 2) ≤ (Real.sqrt T)⁻¹ * ((d : ℝ) * B * K) := by
  calc
    _ ≤ (d : ℝ) * B * Real.sqrt (∑ j, ‖G j‖ ^ 2) :=
      s4_defect_flux_energy_le w hB hm hb G F hF
    _ ≤ ((d : ℝ) * B) * ((Real.sqrt T)⁻¹ * K) :=
      mul_le_mul_of_nonneg_left hG (mul_nonneg (Nat.cast_nonneg d) hB)
    _ = _ := by ring

/-- The force-column defect has the same inverse-square-root time control. -/
theorem s4_defect_column_singular_le {d : ℕ}
    (w : Fin d → Vec d → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hm : ∀ j, Measurable (w j)) (hb : ∀ j x, |w j x| ≤ B)
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (F : Lp ℂ 2 (volume : Measure (Vec d)))
    (hF : ∀ᵐ x ∂volume, F x = ∑ j, ((w j x : ℝ) : ℂ) * G j x)
    {T K : ℝ}
    (hG : Real.sqrt (∑ j, ‖G j‖ ^ 2) ≤ (Real.sqrt T)⁻¹ * K) :
    ‖F‖ ≤ (Real.sqrt T)⁻¹ * (B * Real.sqrt d * K) := by
  calc
    _ ≤ B * (Real.sqrt d * Real.sqrt (∑ j, ‖G j‖ ^ 2)) :=
      s4_defect_ae_energy_le w hB hm hb G F hF
    _ = (B * Real.sqrt d) * Real.sqrt (∑ j, ‖G j‖ ^ 2) := by ring
    _ ≤ (B * Real.sqrt d) * ((Real.sqrt T)⁻¹ * K) :=
      mul_le_mul_of_nonneg_left hG (mul_nonneg hB (Real.sqrt_nonneg _))
    _ = _ := by ring


/-- The actual averaged flux and force column share one gradient and retain
its inverse-square-root energy estimate on every positive intermediate time. -/
theorem s4_physical_averaged_defects_singular {d : ℕ}
    {a b : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ B : ℝ} (hΛ : 0 < Λ) (hell : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (hB : 0 ≤ B)
    (hm : ∀ j k, Measurable (fun x => a x j k - b x j k))
    (hb : ∀ j k x, |a x j k - b x j k| ≤ B)
    (hP : IsPhysicalComplexSemigroup a i ζ P)
    (f : Lp ℂ 2 (volume : Measure (Vec d))) (ε : ℝ≥0)
    (A : Set (Vec d)) (hab : ∀ x ∈ A, a x = b x)
    (t K : ℝ)
    (hgrad : ∀ r ∈ Set.Ioo 0 t, ∀ G,
      IsPhysicalH1Graph volume (Or.inl rfl)
        (P r.toNNReal (s4PhysicalTimeAverage P f ε)) G →
      Real.sqrt (∑ j, ‖G j‖^2) ≤ (Real.sqrt r)⁻¹ * K) :
    ∃ G F : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
    ∃ Q : ℝ → Lp ℂ 2 (volume : Measure (Vec d)),
      (∀ r, IsPhysicalH1Graph volume (Or.inl rfl)
        (P r.toNNReal (s4PhysicalTimeAverage P f ε)) (G r)) ∧
      (∀ j, Continuous (fun r => G r j)) ∧
      (∀ j, Continuous (fun r => F r j)) ∧ Continuous Q ∧
      (∀ r j, ∀ᵐ x ∂volume, F r j x = ∑ k,
        ((a x j k - b x j k : ℝ) : ℂ) * G r k x) ∧
      (∀ r, ∀ᵐ x ∂volume, Q r x = ∑ j,
        ((a x j i - b x j i : ℝ) : ℂ) * G r j x) ∧
      (∀ r j, ∀ᵐ x ∂volume, x ∈ A → F r j x = 0) ∧
      (∀ r, ∀ᵐ x ∂volume, x ∈ A → Q r x = 0) ∧
      (∀ r ∈ Set.Ioo 0 t, Real.sqrt (∑ j, ‖F r j‖^2) ≤
        (Real.sqrt r)⁻¹ * ((d : ℝ) * B * K)) ∧
      ∀ r ∈ Set.Ioo 0 t, ‖Q r‖ ≤
        (Real.sqrt r)⁻¹ * (B * Real.sqrt d * K) := by
  obtain ⟨G, F, Q, hG, hGc, hFc, hQc, hF, hQ, hFs, hQs⟩ :=
    s4_physical_averaged_defects ha hΛ hell hB hm hb hP f ε A hab
  refine ⟨G, F, Q, hG, hGc, hFc, hQc, hF, hQ, hFs, hQs, ?_, ?_⟩
  · intro r hr
    exact s4_defect_flux_singular_le (fun j k x => a x j k - b x j k)
      hB hm hb (G r) (F r) (hF r) (hgrad r hr (G r) (hG r))
  · intro r hr
    exact s4_defect_column_singular_le (fun j x => a x j i - b x j i)
      hB (fun j => hm j i) (fun j => hb j i) (G r) (Q r) (hQ r)
      (hgrad r hr (G r) (hG r))


/-- The localized Duhamel integrand uses the represented flux and column
associated with the same forward gradient. -/
theorem s4_physical_localized_duhamel_defect_representation {d : ℕ}
    {a b : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    {P R T : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (hb : ∀ j k, MemLp (fun x => (b x j k : ℂ)) ∞ volume)
    (hP : IsPhysicalComplexSemigroup a i ζ P)
    (hT : IsPhysicalComplexTransposeSemigroup b i ζ R T)
    (A : Set (Vec d)) (hA : MeasurableSet A) (hab : ∀ x ∈ A, a x = b x)
    (f v : Lp ℂ 2 (volume : Measure (Vec d))) (ε : ℝ≥0) (S : ℝ) (hS : 0 < S)
    (G F : ℝ → Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (Q : ℝ → Lp ℂ 2 (volume : Measure (Vec d)))
    (hG : ∀ r, IsPhysicalH1Graph volume (Or.inl rfl)
      (P r.toNNReal (s4PhysicalTimeAverage P f ε)) (G r))
    (hF : ∀ r j, ∀ᵐ x ∂volume, F r j x = ∑ k,
      ((a x j k - b x j k : ℝ) : ℂ) * G r k x)
    (hQ : ∀ r, ∀ᵐ x ∂volume, Q r x = ∑ j,
      ((a x j i - b x j i : ℝ) : ℂ) * G r j x) :
    ∃ D : ℝ → ℂ, Continuous D ∧
      (∀ r, 0 < r → r < S → ∃ H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalH1Graph volume (Or.inl rfl)
          (T (S-r).toNNReal (s4PhysicalTimeAverage T v ε)) H ∧
        D r = -(1 / 2 : ℂ) * (∫ x in Aᶜ, ∑ j, F r j x * H j x) +
          ζ * (∫ x in Aᶜ, Q r x *
            (T (S-r).toNNReal (s4PhysicalTimeAverage T v ε)) x)) ∧
      (∫ r in (0 : ℝ)..S, D r) =
        s4PhysicalMassPairing (P S.toNNReal (s4PhysicalTimeAverage P f ε))
          (s4PhysicalTimeAverage T v ε) -
        s4PhysicalMassPairing (s4PhysicalTimeAverage P f ε)
          (T S.toNNReal (s4PhysicalTimeAverage T v ε)) := by
  obtain ⟨D, hDc, hD, hI⟩ :=
    s4_physical_localized_averaged_duhamel ha hb hP hT A hA hab f v ε ε S hS
  refine ⟨D, hDc, ?_, hI⟩
  intro r hr hrS
  obtain ⟨G', H, hG', hH, hDr⟩ := hD r hr hrS
  have he : G' = G r := physicalH1Graph_gradient_unique volume (Or.inl rfl)
    _ _ _ hG' (hG r)
  subst G'
  refine ⟨H, hH, ?_⟩
  have hflux : (∫ x in Aᶜ, ∑ j, F r j x * H j x) =
      ∫ x in Aᶜ, ∑ j, ∑ k,
        ((a x j k : ℂ) - (b x j k : ℂ)) * G r k x * H j x := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (ae_all_iff.mpr (hF r))] with x hx
    simp only [hx, Complex.ofReal_sub, Finset.sum_mul]
  have hcol : (∫ x in Aᶜ, Q r x *
      (T (S-r).toNNReal (s4PhysicalTimeAverage T v ε)) x) =
      ∫ x in Aᶜ, (∑ j, ((a x j i : ℂ) - (b x j i : ℂ)) * G r j x) *
        (T (S-r).toNNReal (s4PhysicalTimeAverage T v ε)) x := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (hQ r)] with x hx
    simp only [hx, Complex.ofReal_sub]
  rw [hflux, hcol]
  exact hDr

/-- Dominated convergence for a singular Duhamel time integral. -/
theorem s4_Duhamel_integral_tendsto_zero_of_domination
    (T C : ℝ) (f : ℕ → ℝ → ℂ)
    (hi : IntegrableOn (fun s : ℝ => C * ((Real.sqrt s)⁻¹ *
      (Real.sqrt (T-s))⁻¹)) (Set.Ioo 0 T))
    (hf : ∀ n, AEStronglyMeasurable (f n) (volume.restrict (Set.Ioo 0 T)))
    (hb : ∀ n, ∀ᵐ s ∂volume.restrict (Set.Ioo 0 T),
      ‖f n s‖ ≤ C * ((Real.sqrt s)⁻¹ * (Real.sqrt (T-s))⁻¹))
    (hl : ∀ᵐ s ∂volume.restrict (Set.Ioo 0 T),
      Filter.Tendsto (fun n => f n s) Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun n => ∫ s in Set.Ioo 0 T, f n s) Filter.atTop (𝓝 0) := by
  simpa only [integral_zero] using
    (tendsto_integral_of_dominated_convergence
      (μ := volume.restrict (Set.Ioo 0 T))
      (f := fun _ => (0 : ℂ))
      (fun s => C * ((Real.sqrt s)⁻¹ * (Real.sqrt (T-s))⁻¹)) hf hi hb hl)


/-- Simultaneously approximate two data by strictly positive small time averages. -/
theorem s4_select_two_time_averages {d : ℕ}
    {P T : ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d))}
    (hP0 : P 0 = ContinuousLinearMap.id ℂ _)
    (hT0 : T 0 = ContinuousLinearMap.id ℂ _)
    (hPc : ∀ f, Continuous (fun t => P t f))
    (hTc : ∀ f, Continuous (fun t => T t f))
    (f v : Lp ℂ 2 (volume : Measure (Vec d)))
    (δ : ℝ≥0) (hδ : 0 < δ) (η : ℝ) (hη : 0 < η) :
    ∃ ε : ℝ≥0, 0 < ε ∧ ε < δ ∧
      ‖s4PhysicalTimeAverage P f ε - f‖ < η ∧
      ‖s4PhysicalTimeAverage T v ε - v‖ < η := by
  have hp := s4_physical_time_average_tendsto hP0 hPc f 0
  have ht := s4_physical_time_average_tendsto hT0 hTc v 0
  simp only [hP0, hT0, ContinuousLinearMap.id_apply] at hp ht
  have hp' := (Metric.tendsto_nhds.mp hp) η hη
  have ht' := (Metric.tendsto_nhds.mp ht) η hη
  have hd : ∀ᶠ ε : ℝ≥0 in 𝓝[>] (0 : ℝ≥0), ε < δ :=
    nhdsWithin_le_nhds (Iio_mem_nhds hδ)
  have hz : ∀ᶠ ε : ℝ≥0 in 𝓝[>] (0 : ℝ≥0), 0 < ε := self_mem_nhdsWithin
  obtain ⟨ε, hε, hεd, hεp, hεt⟩ := (hz.and (hd.and (hp'.and ht'))).exists
  exact ⟨ε, hε, hεd, by simpa only [dist_eq_norm] using hεp,
    by simpa only [dist_eq_norm] using hεt⟩

/-- Choose one positive averaging time for each pair of varying data. -/
theorem s4_select_time_averages_for_sequence {d : ℕ}
    (P T : ℕ → ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hP0 : ∀ n, P n 0 = ContinuousLinearMap.id ℂ _)
    (hT0 : ∀ n, T n 0 = ContinuousLinearMap.id ℂ _)
    (hPc : ∀ n f, Continuous (fun t => P n t f))
    (hTc : ∀ n f, Continuous (fun t => T n t f))
    (f v : ℕ → Lp ℂ 2 (volume : Measure (Vec d)))
    (δ : ℕ → ℝ≥0) (hδ : ∀ n, 0 < δ n)
    (η : ℕ → ℝ) (hη : ∀ n, 0 < η n) :
    ∃ ε : ℕ → ℝ≥0, ∀ n, 0 < ε n ∧ ε n < δ n ∧
      ‖s4PhysicalTimeAverage (P n) (f n) (ε n) - f n‖ < η n ∧
      ‖s4PhysicalTimeAverage (T n) (v n) (ε n) - v n‖ < η n := by
  have h : ∀ n, ∃ ε : ℝ≥0, 0 < ε ∧ ε < δ n ∧
      ‖s4PhysicalTimeAverage (P n) (f n) ε - f n‖ < η n ∧
      ‖s4PhysicalTimeAverage (T n) (v n) ε - v n‖ < η n := by
    intro n
    exact s4_select_two_time_averages (hP0 n) (hT0 n) (hPc n) (hTc n)
      (f n) (v n) (δ n) (hδ n) (η n) (hη n)
  exact ⟨fun n => Classical.choose (h n), fun n => Classical.choose_spec (h n)⟩

/-- Tolerances tending to zero give simultaneous convergence of averaging errors. -/
theorem s4_select_time_averages_errors_tendsto_zero {d : ℕ}
    (P T : ℕ → ℝ≥0 → Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ]
      Lp ℂ 2 (volume : Measure (Vec d)))
    (hP0 : ∀ n, P n 0 = ContinuousLinearMap.id ℂ _)
    (hT0 : ∀ n, T n 0 = ContinuousLinearMap.id ℂ _)
    (hPc : ∀ n f, Continuous (fun t => P n t f))
    (hTc : ∀ n f, Continuous (fun t => T n t f))
    (f v : ℕ → Lp ℂ 2 (volume : Measure (Vec d)))
    (δ : ℕ → ℝ≥0) (hδ : ∀ n, 0 < δ n)
    (η : ℕ → ℝ) (hη : ∀ n, 0 < η n)
    (hηlim : Tendsto η atTop (𝓝 0))
    (hδlim : Tendsto δ atTop (𝓝 0)) :
    ∃ ε : ℕ → ℝ≥0, (∀ n, 0 < ε n ∧ ε n < δ n) ∧
      Tendsto ε atTop (𝓝[>] (0 : ℝ≥0)) ∧
      Tendsto (fun n => ‖s4PhysicalTimeAverage (P n) (f n) (ε n) - f n‖)
        atTop (𝓝 0) ∧
      Tendsto (fun n => ‖s4PhysicalTimeAverage (T n) (v n) (ε n) - v n‖)
        atTop (𝓝 0) := by
  obtain ⟨ε, hε⟩ := s4_select_time_averages_for_sequence P T hP0 hT0 hPc hTc
    f v δ hδ η hη
  refine ⟨ε, (fun n => ⟨(hε n).1, (hε n).2.1⟩), ?_, ?_, ?_⟩
  · apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hδlim
      (fun n => (hε n).1.le) (fun n => (hε n).2.1.le), ?_⟩
    exact Filter.Eventually.of_forall (fun n => (hε n).1)
  · exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hε n).2.2.1.le) hηlim
  · exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hε n).2.2.2.le) hηlim
/-- Two norm bounds with vanishing factors give simultaneous pairing limits. -/
theorem s4_pairings_tendsto_zero_of_norm_bounds
    (z q : ℕ → ℂ) (a b : ℕ → ℝ) (A B : ℝ)
    (hz : ∀ n, ‖z n‖ ≤ A * a n) (hq : ∀ n, ‖q n‖ ≤ B * b n)
    (ha : Tendsto a atTop (𝓝 0)) (hb : Tendsto b atTop (𝓝 0)) :
    Tendsto z atTop (𝓝 0) ∧ Tendsto q atTop (𝓝 0) := by
  constructor
  · apply squeeze_zero_norm' (Filter.Eventually.of_forall hz)
    simpa only [mul_zero] using tendsto_const_nhds.mul ha
  · apply squeeze_zero_norm' (Filter.Eventually.of_forall hq)
    simpa only [mul_zero] using tendsto_const_nhds.mul hb

/-- A common Gaussian bound forces both nonnegative defect sizes to vanish. -/
theorem s4_defect_sizes_tendsto_zero_of_gaussian
    (u v r a : ℕ → ℝ) (K A : ℝ) (hK : 0 ≤ K)
    (hu : ∀ n, 0 ≤ u n) (hv : ∀ n, 0 ≤ v n)
    (ha : ∀ n, a n ≤ A)
    (hbound : ∀ n, u n + v n ≤ K * Real.exp (a n - r n))
    (hr : Tendsto r atTop atTop) :
    Tendsto u atTop (𝓝 0) ∧ Tendsto v atTop (𝓝 0) := by
  have hlim : Tendsto (fun n => K * Real.exp (A - r n)) atTop (𝓝 0) := by
    have h := (Real.tendsto_exp_neg_atTop_nhds_zero.comp hr).const_mul
      (K * Real.exp A)
    convert h using 1 <;> simp only [Function.comp_def, mul_zero]
    funext n
    rw [sub_eq_add_neg, Real.exp_add, mul_assoc]
  have hbound' (n : ℕ) : u n + v n ≤ K * Real.exp (A - r n) :=
    (hbound n).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (sub_le_sub_right (ha n) _)) hK)
  constructor
  · apply squeeze_zero hu _ hlim
    intro n
    linarith [hbound' n, hv n]
  · apply squeeze_zero hv _ hlim
    intro n
    linarith [hbound' n, hu n]

/-- The Gaussian localization exponent diverges for growing radii and bounded windows. -/
theorem s4_gaussian_exponent_tendsto_atTop
    (ρ ε : ℕ → ℝ) (s E c : ℝ) (hs : 0 < s) (hE : 0 ≤ E) (hc : 0 < c)
    (hε0 : ∀ n, 0 ≤ ε n) (hεE : ∀ n, ε n ≤ E)
    (hρ : Tendsto ρ atTop atTop) :
    Tendsto (fun n => c * ρ n ^ 2 / (s + ε n)) atTop atTop := by
  have htop : Tendsto (fun n => (c / (s + E)) * ρ n ^ 2) atTop atTop := by
    simpa only [Function.comp_def] using
      ((tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp hρ).const_mul_atTop
        (div_pos hc (add_pos_of_pos_of_nonneg hs hE))
  apply tendsto_atTop_mono (fun n => ?_) htop
  calc
    (c / (s + E)) * ρ n ^ 2 = (c * ρ n ^ 2) / (s + E) := by ring
    _ ≤ (c * ρ n ^ 2) / (s + ε n) :=
      div_le_div_of_nonneg_left (mul_nonneg hc.le (sq_nonneg _))
        (add_pos_of_pos_of_nonneg hs (hε0 n)) (add_le_add le_rfl (hεE n))

/-- Gaussian defect-size decay and uniform test bounds give both pairing limits. -/
theorem s4_pairings_tendsto_zero_of_gaussian
    (z q : ℕ → ℂ) (u v r a : ℕ → ℝ) (K A B D : ℝ) (hK : 0 ≤ K)
    (hu : ∀ n, 0 ≤ u n) (hv : ∀ n, 0 ≤ v n)
    (ha : ∀ n, a n ≤ A)
    (hbound : ∀ n, u n + v n ≤ K * Real.exp (a n - r n))
    (hr : Tendsto r atTop atTop)
    (hz : ∀ n, ‖z n‖ ≤ B * u n) (hq : ∀ n, ‖q n‖ ≤ D * v n) :
    Tendsto z atTop (𝓝 0) ∧ Tendsto q atTop (𝓝 0) := by
  obtain ⟨hu0, hv0⟩ := s4_defect_sizes_tendsto_zero_of_gaussian
    u v r a K A hK hu hv ha hbound hr
  exact s4_pairings_tendsto_zero_of_norm_bounds z q u v B D hz hq hu0 hv0

/-- Growing localization radii make both controlled pairings vanish together. -/
theorem s4_pairings_tendsto_zero_of_growing_radius
    (z q : ℕ → ℂ) (u v a ρ ε : ℕ → ℝ) (K A B D s E c : ℝ)
    (hK : 0 ≤ K) (hs : 0 < s) (hE : 0 ≤ E) (hc : 0 < c)
    (hε0 : ∀ n, 0 ≤ ε n) (hεE : ∀ n, ε n ≤ E)
    (hρ : Tendsto ρ atTop atTop)
    (hu : ∀ n, 0 ≤ u n) (hv : ∀ n, 0 ≤ v n) (ha : ∀ n, a n ≤ A)
    (hbound : ∀ n, u n + v n ≤ K * Real.exp
      (a n - c * ρ n ^ 2 / (s + ε n)))
    (hz : ∀ n, ‖z n‖ ≤ B * u n) (hq : ∀ n, ‖q n‖ ≤ D * v n) :
    Tendsto z atTop (𝓝 0) ∧ Tendsto q atTop (𝓝 0) := by
  exact s4_pairings_tendsto_zero_of_gaussian z q u v
    (fun n => c * ρ n ^ 2 / (s + ε n)) a K A B D hK hu hv ha hbound
    (s4_gaussian_exponent_tendsto_atTop ρ ε s E c hs hE hc hε0 hεE hρ) hz hq

end EinsteinFull
