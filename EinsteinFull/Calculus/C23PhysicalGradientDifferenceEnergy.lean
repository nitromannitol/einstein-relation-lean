import EinsteinFull.Calculus.C18PhysicalEvolutionSmoothing
import EinsteinFull.Calculus.S5WeightSupport

open MeasureTheory
open scoped NNReal ENNReal BigOperators Topology

namespace EinsteinFull
open EinsteinRelation

/-- The forward coordinate difference quotient retains the given physical
H1 gradient, with each component replaced by its forward quotient. -/
theorem c23_physical_forward_difference_quotient_graph {d : ℕ}
    {f : Lp ℂ 2 (volume : Measure (Vec d))}
    {G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G) (l : Fin d) (h : ℝ) :
    ∃ (q : Lp ℂ 2 (volume : Measure (Vec d)))
      (Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) q Q ∧
      (q : Vec d → ℂ) =ᵐ[volume]
        (fun x => (f (x + h • unitVector l) - f x) / (h : ℂ)) ∧
      (∀ j, (Q j : Vec d → ℂ) =ᵐ[volume]
        (fun x => (G j (x + h • unitVector l) - G j x) / (h : ℂ))) ∧
      ∀ j, ((eLpNorm (fun x => (G j (x + h • unitVector l) - G j x) /
        (h : ℂ)) 2 (volume : Measure (Vec d))).toReal) = ‖Q j‖ := by
  obtain ⟨q, Q, hqQ, hq, hQ⟩ :=
    c18_physical_H1_difference_quotient hG (-(h • unitVector l)) h
  have hQ' : ∀ j, (Q j : Vec d → ℂ) =ᵐ[volume]
      (fun x => (G j (x + h • unitVector l) - G j x) / (h : ℂ)) := by
    intro j
    simpa only [sub_neg_eq_add, div_eq_mul_inv, mul_comm] using hQ j
  refine ⟨q, Q, hqQ, ?_, hQ', ?_⟩
  · simpa only [sub_neg_eq_add, div_eq_mul_inv, mul_comm] using hq
  · intro j
    rw [← eLpNorm_congr_ae (hQ' j), ← Lp.norm_def]

/-- The quotient representative in the forward graph has the sharp bound
by the corresponding component of the supplied gradient. -/
theorem c23_forward_difference_quotient_norm_le {d : ℕ}
    {f q : Lp ℂ 2 (volume : Measure (Vec d))}
    {G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    (l : Fin d) (h : ℝ) (hh : h ≠ 0)
    (hq : (q : Vec d → ℂ) =ᵐ[volume]
      (fun x => (f (x + h • unitVector l) - f x) / (h : ℂ))) :
    ‖q‖ ≤ ‖G l‖ := by
  have hb := c18_physical_H1_coordinate_difference_quotient_bound hG l h hh
  rw [← eLpNorm_congr_ae hq, ← Lp.norm_def] at hb
  exact hb

/-- The backward quotient obeys the same sharp H1 bound for a signed step. -/
theorem c23_physical_H1_backward_quotient_bound {d : ℕ}
    {f : Lp ℂ 2 (volume : Measure (Vec d))}
    {G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    (l : Fin d) (h : ℝ) (hh : h ≠ 0) :
    ((eLpNorm (fun x => (f (x - h • unitVector l) - f x) / (h : ℂ))
      2 (volume : Measure (Vec d))).toReal) ≤ ‖G l‖ := by
  have he : (fun x => (f (x - h • unitVector l) - f x) / (h : ℂ)) =
      -(fun x => (f (x + (-h) • unitVector l) - f x) / ((-h : ℝ) : ℂ)) := by
    funext x
    simp only [Pi.neg_apply, neg_smul, sub_eq_add_neg, Complex.ofReal_neg,
      div_neg, neg_neg]
  rw [he, eLpNorm_neg]
  exact c18_physical_H1_coordinate_difference_quotient_bound hG l (-h) (neg_ne_zero.mpr hh)

/-- A backward test representative inherits the sharp bound from its H1
argument, independently of the signed step. -/
theorem c23_backward_test_norm_le {d : ℕ}
    {v r : Lp ℂ 2 (volume : Measure (Vec d))}
    {H : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hH : IsPhysicalH1Graph volume (Or.inl rfl) v H)
    (l : Fin d) (h : ℝ) (hh : h ≠ 0)
    (hr : (r : Vec d → ℂ) =ᵐ[volume]
      (fun x => (h : ℂ)⁻¹ * (v (x - h • unitVector l) - v x))) :
    ‖r‖ ≤ ‖H l‖ := by
  have hb := c23_physical_H1_backward_quotient_bound hH l h hh
  have hr' : (r : Vec d → ℂ) =ᵐ[volume]
      (fun x => (v (x - h • unitVector l) - v x) / (h : ℂ)) := by
    simpa only [div_eq_mul_inv, mul_comm] using hr
  rw [← eLpNorm_congr_ae hr', ← Lp.norm_def] at hb
  exact hb

/-- Complex conjugation preserves the L² norm. -/
theorem c23_L2_norm_star {d : ℕ}
    (u : Lp ℂ 2 (volume : Measure (Vec d))) : ‖star u‖ = ‖u‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (Lp.coeFn_star u), eLpNorm_star]

/-- A backward quotient of the conjugate of the forward quotient can be
used as an H1 test, with its L² norm controlled by the quotient gradient. -/
theorem c23_conjugate_backward_energy_test {d : ℕ}
    {q : Lp ℂ 2 (volume : Measure (Vec d))}
    {Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hQ : IsPhysicalH1Graph volume (Or.inl rfl) q Q)
    (l : Fin d) (h : ℝ) (hh : h ≠ 0) :
    ∃ (r : Lp ℂ 2 (volume : Measure (Vec d)))
      (R : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) r R ∧
      (r : Vec d → ℂ) =ᵐ[volume]
        (fun x => (h : ℂ)⁻¹ * ((star q) (x - h • unitVector l) - (star q) x)) ∧
      (∀ j, (R j : Vec d → ℂ) =ᵐ[volume]
        (fun x => (h : ℂ)⁻¹ * ((star (Q j)) (x - h • unitVector l) - (star (Q j)) x))) ∧
      ‖r‖ ≤ ‖Q l‖ := by
  have hs := physicalH1Graph_star q Q hQ
  obtain ⟨r, R, hrR, hr, hR⟩ :=
    c18_physical_H1_difference_quotient hs (h • unitVector l) h
  refine ⟨r, R, hrR, hr, hR, ?_⟩
  simpa only [c23_L2_norm_star] using c23_backward_test_norm_le hs l h hh hr

/-- The forcing term paired with a backward energy test is controlled by
the corresponding component of the forward quotient gradient. -/
theorem c23_backward_energy_forcing_bound {d : ℕ}
    {q r g : Lp ℂ 2 (volume : Measure (Vec d))}
    {Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hQ : IsPhysicalH1Graph volume (Or.inl rfl) q Q)
    (l : Fin d) (h : ℝ) (hh : h ≠ 0)
    (hr : (r : Vec d → ℂ) =ᵐ[volume]
      (fun x => (h : ℂ)⁻¹ * ((star q) (x - h • unitVector l) - (star q) x))) :
    ‖∫ x, g x * r x‖ ≤ ‖g‖ * ‖Q l‖ := by
  have htest : ‖r‖ ≤ ‖Q l‖ := by
    simpa only [c23_L2_norm_star] using
      c23_backward_test_norm_le (physicalH1Graph_star q Q hQ) l h hh hr
  have hpair : (∫ x, g x * r x) = inner ℂ (star r) g := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_star r] with x hx
    simp only [hx, RCLike.inner_apply, Pi.star_apply, Complex.star_def,
      Complex.conj_conj, mul_comm]
  rw [hpair]
  calc
    ‖inner ℂ (star r) g‖ ≤ ‖star r‖ * ‖g‖ := norm_inner_le_norm _ _
    _ ≤ ‖Q l‖ * ‖g‖ := by
      simpa only [c23_L2_norm_star] using mul_le_mul_of_nonneg_right htest (norm_nonneg g)
    _ = ‖g‖ * ‖Q l‖ := mul_comm _ _

/-- Integrated ellipticity controls the squared L² norms of an arbitrary
complex vector field by its principal quadratic pairing. -/
theorem c23_integrated_principal_coercivity {d : ℕ}
    (a : Vec d → Mat d) {Λ : ℝ}
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :
    Λ⁻¹ * (∑ j, ‖Q j‖ ^ 2) ≤
      (∫ x, ∑ j, ∑ k, (a x j k : ℂ) * Q k x * star (Q j x)).re := by
  let P : Vec d → ℂ := fun x => ∑ j, ∑ k,
    (a x j k : ℂ) * Q k x * star (Q j x)
  have hP : Integrable P volume := by
    apply integrable_finsetSum Finset.univ
    intro j _
    apply integrable_finsetSum Finset.univ
    intro k _
    exact ((ha j k).mul (r := 2) (Lp.memLp (Q k))).integrable_mul (Lp.memLp (Q j)).star
  have hN : Integrable (fun x => ∑ j, ‖Q j x‖ ^ 2) volume :=
    integrable_finsetSum _ fun j _ => (Lp.memLp (Q j)).norm.integrable_sq
  have hp : ∀ᵐ x ∂volume, Λ⁻¹ * (∑ j, ‖Q j x‖ ^ 2) ≤ (P x).re := by
    filter_upwards [hA] with x hx
    exact s5_coercive hx (fun j => Q j x)
  have hi := integral_mono_ae (hN.const_mul Λ⁻¹) hP.re hp
  have hnorm : (∫ x, ∑ j, ‖Q j x‖ ^ 2) = ∑ j, ‖Q j‖ ^ 2 := by
    rw [integral_finsetSum _ fun j _ => (Lp.memLp (Q j)).norm.integrable_sq]
    exact Finset.sum_congr rfl fun j _ => (physicalL2_norm_sq volume (Q j)).symm
  have hre := integral_re hP
  simp only [RCLike.re_eq_complex_re] at hre
  simp only [RCLike.re_eq_complex_re] at hi
  rw [integral_const_mul, hnorm, hre] at hi
  exact hi

/-- Ellipticity and boundedness survive translation by the signed
difference-quotient step, giving the principal energy estimate. -/
theorem c23_translated_principal_coercivity {d : ℕ}
    (a : Vec d → Mat d) {Λ : ℝ}
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) (z : Vec d) :
    Λ⁻¹ * (∑ j, ‖Q j‖ ^ 2) ≤
      (∫ x, ∑ j, ∑ k, (a (x + z) j k : ℂ) * Q k x * star (Q j x)).re := by
  have hp := measurePreserving_add_right (volume : Measure (Vec d)) z
  have hat : ∀ j k, MemLp (fun x => (a (x + z) j k : ℂ)) ∞ volume := by
    intro j k
    simpa only [Function.comp_def] using (ha j k).comp_measurePreserving hp
  have hAt : ∀ᵐ x ∂volume, S5Elliptic (a (x + z)) Λ :=
    hp.quasiMeasurePreserving.ae hA
  exact c23_integrated_principal_coercivity (fun x => a (x + z)) hat hAt Q

/-- The generator graph estimate applies to the particular supplied weak
gradient, for either orientation of the actual physical generator. -/
theorem c23_supplied_gradient_graph_bound {d : ℕ} (a : Vec d → Mat d)
    (i : Fin d) (ζ : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {Λ : ℝ} (hΛ : 0 < Λ) (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexGeneratorPair a i ζ f g ∨
      IsPhysicalComplexTransposeGeneratorPair a i ζ f g)
    {G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G) :
    (∑ j, ‖G j‖ ^ 2) ≤ 4 * Λ * ‖f‖ * ‖g‖ +
      4 * ((d : ℝ) + 1) ^ 2 * Λ ^ 4 * ‖ζ‖ ^ 2 * ‖f‖ ^ 2 := by
  have hb : ∃ G' : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) f G' ∧
      (∑ j, ‖G' j‖ ^ 2) ≤ 4 * Λ * ‖f‖ * ‖g‖ +
        4 * ((d : ℝ) + 1) ^ 2 * Λ ^ 4 * ‖ζ‖ ^ 2 * ‖f‖ ^ 2 := by
    rcases hfg with hf | hf
    · exact Blueprint.physical_complex_generator_gradient_bound a i ζ ha hΛ hA hf
    · exact Blueprint.physical_complex_transpose_generator_gradient_bound a i ζ ha hΛ hA hf
  obtain ⟨G', hG', hb⟩ := hb
  rw [physicalH1Graph_gradient_unique volume (Or.inl rfl) f G' G hG' hG] at hb
  exact hb

/-- A coefficient difference quotient acts on L² with the structural
first-derivative bound, uniformly in the signed nonzero step. -/
theorem c23_coefficient_quotient_multiplier {d : ℕ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hsmooth : IsSmoothWithBounds M ω)
    (l j k : Fin d) {h : ℝ} (hh : h ≠ 0)
    (u : Lp ℂ 2 (volume : Measure (Vec d))) :
    ∃ v : Lp ℂ 2 (volume : Measure (Vec d)),
      (v : Vec d → ℂ) =ᵐ[volume]
        (fun x => (((ω.1 (x + h • unitVector l) j k - ω.1 x j k) / h : ℝ) : ℂ) * u x) ∧
      ‖v‖ ≤ M 1 * ‖u‖ := by
  let w : Vec d → ℝ := fun x => (ω.1 (x + h • unitVector l) j k - ω.1 x j k) / h
  have hw : Measurable w := by
    apply Continuous.measurable
    exact (((hsmooth.1.1 j k).continuous.comp (continuous_id.add continuous_const)).sub
      (hsmooth.1.1 j k).continuous).div_const h
  have hM : 0 ≤ M 1 := (c18_smooth_coefficient_divergence_bounds hsmooth).1
  have hb : ∀ x, |w x| ≤ M 1 := fun x =>
    c18_smooth_coefficient_coordinate_quotient_bound hsmooth l j k x hh
  let v := (s5_memLp_mul hw hb u).toLp (fun x => (w x : ℂ) * u x)
  refine ⟨v, (s5_memLp_mul hw hb u).coeFn_toLp, ?_⟩
  rw [Lp.norm_toLp, Lp.norm_def]
  have he := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (μ := (volume : Measure (Vec d)))
      (f := fun x => (w x : ℂ) * u x) (g := (u : Vec d → ℂ)) (c := M 1)
      ((Complex.measurable_ofReal.comp hw).aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable u))
      (Filter.Eventually.of_forall fun x => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)) 2
  calc (eLpNorm (fun x => (w x : ℂ) * u x) 2 volume).toReal
      ≤ (ENNReal.ofReal (M 1) * eLpNorm (u : Vec d → ℂ) 2 volume).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top u)) he
    _ = M 1 * (eLpNorm (u : Vec d → ℂ) 2 volume).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM]

/-- The coefficient commutator is bounded when paired against any L² test. -/
theorem c23_coefficient_quotient_pairing_bound {d : ℕ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hsmooth : IsSmoothWithBounds M ω)
    (l j k : Fin d) {h : ℝ} (hh : h ≠ 0)
    (u v : Lp ℂ 2 (volume : Measure (Vec d))) :
    ‖∫ x, (((ω.1 (x + h • unitVector l) j k - ω.1 x j k) / h : ℝ) : ℂ) *
      u x * star (v x)‖ ≤ M 1 * ‖u‖ * ‖v‖ := by
  obtain ⟨w, hw, hbound⟩ := c23_coefficient_quotient_multiplier hsmooth l j k hh u
  have hpair : (∫ x, (((ω.1 (x + h • unitVector l) j k - ω.1 x j k) / h : ℝ) : ℂ) *
      u x * star (v x)) = inner ℂ v w := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hw] with x hx
    simp only [RCLike.inner_apply, Complex.star_def]
    rw [hx]
  rw [hpair]
  calc
    ‖inner ℂ v w‖ ≤ ‖v‖ * ‖w‖ := norm_inner_le_norm _ _
    _ ≤ ‖v‖ * (M 1 * ‖u‖) := mul_le_mul_of_nonneg_left hbound (norm_nonneg _)
    _ = M 1 * ‖u‖ * ‖v‖ := by ring

/-- Product rule for a signed forward quotient, with the original function
in the coefficient commutator and the translated coefficient in the
principal term. The identity also holds at a zero step. -/
theorem c23_forward_difference_quotient_mul {d : ℕ}
    (a u : Vec d → ℂ) (l : Fin d) (h : ℝ) (x : Vec d) :
    (a (x + h • unitVector l) * u (x + h • unitVector l) - a x * u x) /
        (h : ℂ) =
      a (x + h • unitVector l) *
          ((u (x + h • unitVector l) - u x) / (h : ℂ)) +
        ((a (x + h • unitVector l) - a x) / (h : ℂ)) * u x := by
  simp only [div_eq_mul_inv]
  ring

/-- Discrete integration by parts followed by the product rule separates the
translated principal coefficient from its coefficient commutator. -/
theorem c23_difference_quotient_product_integration_by_parts {d : ℕ}
    (a : Vec d → ℂ) (ha : MemLp a ∞ (volume : Measure (Vec d)))
    (u v : Lp ℂ 2 (volume : Measure (Vec d))) (l : Fin d) (h : ℝ) :
    (∫ x, a x * u x * ((v (x - h • unitVector l) - v x) / (h : ℂ))) =
      (∫ x, a (x + h • unitVector l) *
        ((u (x + h • unitVector l) - u x) / (h : ℂ)) * v x) +
      (∫ x, ((a (x + h • unitVector l) - a x) / (h : ℂ)) * u x * v x) := by
  let z : Vec d := h • unitVector l
  have hat : MemLp (fun x => a (x + z)) ∞ volume := by
    simpa only [Function.comp_def] using
      ha.comp_measurePreserving (measurePreserving_add_right (volume : Measure (Vec d)) z)
  have hda : MemLp (fun x => (a (x + z) - a x) / (h : ℂ)) ∞ volume := by
    simpa only [div_eq_mul_inv, mul_comm, Pi.sub_apply] using
      (hat.sub ha).const_mul ((h : ℂ)⁻¹)
  have hdu : MemLp (fun x => (u (x + z) - u x) / (h : ℂ)) 2 volume := by
    exact c18_L2_coordinate_difference_quotient_memLp u l h
  have h₁ : Integrable (fun x => a (x + z) * ((u (x + z) - u x) / (h : ℂ)) * v x) :=
    (hat.mul (r := 2) hdu).integrable_mul (Lp.memLp v)
  have h₂ : Integrable (fun x => ((a (x + z) - a x) / (h : ℂ)) * u x * v x) :=
    (hda.mul (r := 2) (Lp.memLp u)).integrable_mul (Lp.memLp v)
  have hi := c18_L2_difference_quotient_integration_by_parts
    (ha.mul (r := 2) (Lp.memLp u)) (Lp.memLp v) z h
  simp only [Pi.mul_apply] at hi
  have he : (fun x => ((a (x + z) * u (x + z) - a x * u x) / (h : ℂ)) * v x) =
      (fun x => a (x + z) * ((u (x + z) - u x) / (h : ℂ)) * v x +
        ((a (x + z) - a x) / (h : ℂ)) * u x * v x) := by
    funext x
    rw [show ((a (x + z) * u (x + z) - a x * u x) / (h : ℂ)) =
      a (x + z) * ((u (x + z) - u x) / (h : ℂ)) +
        ((a (x + z) - a x) / (h : ℂ)) * u x from
      c23_forward_difference_quotient_mul a u l h x]
    ring
  rw [he, integral_add h₁ h₂] at hi
  exact hi.symm

/-- Summation by parts expressed using the actual L² quotient representatives
and the conjugate backward test. -/
theorem c23_principal_quotient_pairing_identity {d : ℕ}
    (a : Vec d → ℂ) (ha : MemLp a ∞ (volume : Measure (Vec d)))
    (u v D r : Lp ℂ 2 (volume : Measure (Vec d))) (l : Fin d) (h : ℝ)
    (hD : (D : Vec d → ℂ) =ᵐ[volume]
      (fun x => (u (x + h • unitVector l) - u x) / (h : ℂ)))
    (hr : (r : Vec d → ℂ) =ᵐ[volume]
      (fun x => (h : ℂ)⁻¹ * ((star v) (x - h • unitVector l) - (star v) x))) :
    (∫ x, a x * u x * r x) =
      (∫ x, a (x + h • unitVector l) * D x * star (v x)) +
      (∫ x, ((a (x + h • unitVector l) - a x) / (h : ℂ)) * u x * star (v x)) := by
  have hi := c23_difference_quotient_product_integration_by_parts a ha u (star v) l h
  calc
    (∫ x, a x * u x * r x) =
        ∫ x, a x * u x * (((star v) (x - h • unitVector l) - (star v) x) / (h : ℂ)) := by
          apply integral_congr_ae
          filter_upwards [hr] with x hx
          rw [hx]
          simp only [div_eq_mul_inv]
          ring
    _ = (∫ x, a (x + h • unitVector l) *
        ((u (x + h • unitVector l) - u x) / (h : ℂ)) * (star v) x) +
        (∫ x, ((a (x + h • unitVector l) - a x) / (h : ℂ)) * u x * (star v) x) := hi
    _ = (∫ x, a (x + h • unitVector l) * D x * star (v x)) +
        (∫ x, ((a (x + h • unitVector l) - a x) / (h : ℂ)) * u x * star (v x)) := by
          congr 1
          · apply integral_congr_ae
            filter_upwards [hD, Lp.coeFn_star v] with x hx hv
            simp only [hx, hv, Pi.star_apply]
          · apply integral_congr_ae
            filter_upwards [Lp.coeFn_star v] with x hv
            simp only [hv, Pi.star_apply]

/-- Absorb a linear commutator term into a coercive quadratic energy. -/
theorem c23_absorb_quadratic_energy (a A B x y : ℝ) (ha : 0 ≤ a)
    (henergy : a * x ^ 2 ≤ A * x * y + B * y ^ 2) :
    a ^ 2 * x ^ 2 ≤ (A ^ 2 + 2 * a * B) * y ^ 2 := by
  have h := mul_nonneg ha (sub_nonneg.mpr henergy)
  have hs := sq_nonneg (a * x - A * y)
  nlinarith

/-- The forward generator admits the conjugate backward energy test, and
its principal term has the translated-coefficient quotient decomposition. -/
theorem c23_forward_generator_quotient_energy_test {d : ℕ}
    {a : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    {G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexGeneratorPair a i ζ f g)
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    (l : Fin d) (h : ℝ) :
    ∃ (q r : Lp ℂ 2 (volume : Measure (Vec d)))
      (Q R : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) q Q ∧
      (q : Vec d → ℂ) =ᵐ[volume]
        (fun x => (f (x + h • unitVector l) - f x) / (h : ℂ)) ∧
      (∀ j, (Q j : Vec d → ℂ) =ᵐ[volume]
        (fun x => (G j (x + h • unitVector l) - G j x) / (h : ℂ))) ∧
      (r : Vec d → ℂ) =ᵐ[volume]
        (fun x => (h : ℂ)⁻¹ * ((star q) (x - h • unitVector l) - (star q) x)) ∧
      (∫ x, g x * r x) =
        -(1 / 2 : ℂ) * (∫ x, ∑ j, ∑ k, (a x j k : ℂ) * G k x * R j x) +
        ζ * (∫ x, (∑ j, (a x j i : ℂ) * G j x) * r x) ∧
      ∀ j k, (∫ x, (a x j k : ℂ) * G k x * R j x) =
        (∫ x, (a (x + h • unitVector l) j k : ℂ) * Q k x * star (Q j x)) +
        (∫ x, (((a (x + h • unitVector l) j k : ℂ) - (a x j k : ℂ)) /
          (h : ℂ)) * G k x * star (Q j x)) := by
  obtain ⟨q, Q, hqQ, hq, hQ, _⟩ :=
    c23_physical_forward_difference_quotient_graph hG l h
  obtain ⟨r, R, _, hr, hR, hweak⟩ :=
    c18_physical_generator_backward_quotient_test hfg hG
      (physicalH1Graph_star q Q hqQ) l h
  refine ⟨q, r, Q, R, hqQ, hq, hQ, hr, hweak, ?_⟩
  intro j k
  exact c23_principal_quotient_pairing_identity (fun x => (a x j k : ℂ))
    (ha j k) (G k) (Q j) (Q k) (R j) l h (hQ k) (hR j)

/-- The transpose generator has the corresponding energy test, with the
principal coefficients in their actual transposed order. -/
theorem c23_transpose_generator_quotient_energy_test {d : ℕ}
    {a : Vec d → Mat d} {i : Fin d} {ζ : ℂ}
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    {G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexTransposeGeneratorPair a i ζ f g)
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    (l : Fin d) (h : ℝ) :
    ∃ (q r : Lp ℂ 2 (volume : Measure (Vec d)))
      (Q R : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) q Q ∧
      (q : Vec d → ℂ) =ᵐ[volume]
        (fun x => (f (x + h • unitVector l) - f x) / (h : ℂ)) ∧
      (∀ j, (Q j : Vec d → ℂ) =ᵐ[volume]
        (fun x => (G j (x + h • unitVector l) - G j x) / (h : ℂ))) ∧
      (r : Vec d → ℂ) =ᵐ[volume]
        (fun x => (h : ℂ)⁻¹ * ((star q) (x - h • unitVector l) - (star q) x)) ∧
      (∫ x, g x * r x) =
        -(1 / 2 : ℂ) * (∫ x, ∑ j, ∑ k, (a x k j : ℂ) * G k x * R j x) +
        ζ * (∫ x, f x * (∑ j, (a x j i : ℂ) * R j x)) ∧
      ∀ j k, (∫ x, (a x k j : ℂ) * G k x * R j x) =
        (∫ x, (a (x + h • unitVector l) k j : ℂ) * Q k x * star (Q j x)) +
        (∫ x, (((a (x + h • unitVector l) k j : ℂ) - (a x k j : ℂ)) /
          (h : ℂ)) * G k x * star (Q j x)) := by
  obtain ⟨q, Q, hqQ, hq, hQ, _⟩ :=
    c23_physical_forward_difference_quotient_graph hG l h
  obtain ⟨r, R, _, hr, hR, hweak⟩ :=
    c18_physical_transpose_generator_backward_quotient_test hfg hG
      (physicalH1Graph_star q Q hqQ) l h
  refine ⟨q, r, Q, R, hqQ, hq, hQ, hr, hweak, ?_⟩
  intro j k
  exact c23_principal_quotient_pairing_identity (fun x => (a x k j : ℂ))
    (ha k j) (G k) (Q j) (Q k) (R j) l h (hQ k) (hR j)

/-- Componentwise integral identities combine into the corresponding finite
principal and commutator sums. -/
theorem c23_integral_double_sum_split {d : ℕ}
    (F P E : Fin d → Fin d → Vec d → ℂ)
    (hF : ∀ j k, Integrable (F j k) volume)
    (hP : ∀ j k, Integrable (P j k) volume)
    (hE : ∀ j k, Integrable (E j k) volume)
    (hpair : ∀ j k, (∫ x, F j k x) = (∫ x, P j k x) + ∫ x, E j k x) :
    (∫ x, ∑ j, ∑ k, F j k x) =
      (∫ x, ∑ j, ∑ k, P j k x) + ∫ x, ∑ j, ∑ k, E j k x := by
  have hcollect (T : Fin d → Fin d → Vec d → ℂ)
      (hT : ∀ j k, Integrable (T j k) volume) :
      (∫ x, ∑ j, ∑ k, T j k x) = ∑ j, ∑ k, ∫ x, T j k x := by
    rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hT j k))]
    apply Finset.sum_congr rfl
    intro j _
    exact integral_finsetSum _ (fun k _ => hT j k)
  rw [hcollect F hF, hcollect P hP, hcollect E hE]
  simp_rw [hpair, Finset.sum_add_distrib]

/-- Translated coercivity also holds for the bilinear transpose principal
form, with the same ellipticity constant. -/
theorem c23_translated_transpose_principal_coercivity {d : ℕ}
    (a : Vec d → Mat d) {Λ : ℝ}
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    (hA : ∀ᵐ x ∂volume, S5Elliptic (a x) Λ)
    (Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) (z : Vec d) :
    Λ⁻¹ * (∑ j, ‖Q j‖ ^ 2) ≤
      (∫ x, ∑ j, ∑ k, (a (x + z) k j : ℂ) * Q k x * star (Q j x)).re := by
  have hc := c23_translated_principal_coercivity a ha hA (fun j => star (Q j)) z
  have he : (∫ x, ∑ j, ∑ k, (a (x + z) j k : ℂ) *
      (star (Q k)) x * star ((star (Q j)) x)) =
      ∫ x, ∑ j, ∑ k, (a (x + z) k j : ℂ) * Q k x * star (Q j x) := by
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr (fun j => Lp.coeFn_star (Q j))] with x hx
    simp only [hx, Pi.star_apply, Complex.star_def, Complex.conj_conj]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp only [c23_L2_norm_star] at hc
  rw [he] at hc
  exact hc

/-- The sum of the component L² norms is bounded in terms of their
squared energy. -/
theorem c23_sum_L2_norm_sq_le {d : ℕ}
    (U : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :
    (∑ j, ‖U j‖) ^ 2 ≤ (d : ℝ) * ∑ j, ‖U j‖ ^ 2 := by
  simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : Fin d => (1 : ℝ)) (fun j => ‖U j‖)

/-- The full coefficient commutator sum is controlled by the product of
the component L² norm sums, uniformly in the signed step. -/
theorem c23_coefficient_quotient_sum_bound {d : ℕ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hsmooth : IsSmoothWithBounds M ω)
    (l : Fin d) {h : ℝ} (hh : h ≠ 0)
    (G Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :
    ‖∑ j, ∑ k, ∫ x,
      (((ω.1 (x + h • unitVector l) j k - ω.1 x j k) / h : ℝ) : ℂ) *
        G k x * star (Q j x)‖ ≤
      M 1 * (∑ k, ‖G k‖) * (∑ j, ‖Q j‖) := by
  calc
    ‖∑ j, ∑ k, ∫ x,
      (((ω.1 (x + h • unitVector l) j k - ω.1 x j k) / h : ℝ) : ℂ) *
        G k x * star (Q j x)‖ ≤
        ∑ j, ‖∑ k, ∫ x,
          (((ω.1 (x + h • unitVector l) j k - ω.1 x j k) / h : ℝ) : ℂ) *
            G k x * star (Q j x)‖ := norm_sum_le _ _
    _ ≤ ∑ j, ∑ k, ‖∫ x,
          (((ω.1 (x + h • unitVector l) j k - ω.1 x j k) / h : ℝ) : ℂ) *
            G k x * star (Q j x)‖ := by
      apply Finset.sum_le_sum
      intro j _
      exact norm_sum_le _ _
    _ ≤ ∑ j, ∑ k, M 1 * ‖G k‖ * ‖Q j‖ := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      exact c23_coefficient_quotient_pairing_bound hsmooth l j k hh (G k) (Q j)
    _ = M 1 * (∑ k, ‖G k‖) * (∑ j, ‖Q j‖) := by
      simp only [← Finset.sum_mul, ← Finset.mul_sum]

/-- The transposed coefficient commutator obeys the same sum bound. -/
theorem c23_transpose_coefficient_quotient_sum_bound {d : ℕ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hsmooth : IsSmoothWithBounds M ω)
    (l : Fin d) {h : ℝ} (hh : h ≠ 0)
    (G Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :
    ‖∑ j, ∑ k, ∫ x,
      (((ω.1 (x + h • unitVector l) k j - ω.1 x k j) / h : ℝ) : ℂ) *
        G k x * star (Q j x)‖ ≤
      M 1 * (∑ k, ‖G k‖) * (∑ j, ‖Q j‖) := by
  calc
    ‖∑ j, ∑ k, ∫ x,
      (((ω.1 (x + h • unitVector l) k j - ω.1 x k j) / h : ℝ) : ℂ) *
        G k x * star (Q j x)‖ ≤
        ∑ j, ‖∑ k, ∫ x,
          (((ω.1 (x + h • unitVector l) k j - ω.1 x k j) / h : ℝ) : ℂ) *
            G k x * star (Q j x)‖ := norm_sum_le _ _
    _ ≤ ∑ j, ∑ k, ‖∫ x,
          (((ω.1 (x + h • unitVector l) k j - ω.1 x k j) / h : ℝ) : ℂ) *
            G k x * star (Q j x)‖ := by
      apply Finset.sum_le_sum
      intro j _
      exact norm_sum_le _ _
    _ ≤ ∑ j, ∑ k, M 1 * ‖G k‖ * ‖Q j‖ := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      exact c23_coefficient_quotient_pairing_bound hsmooth l k j hh (G k) (Q j)
    _ = M 1 * (∑ k, ‖G k‖) * (∑ j, ‖Q j‖) := by
      simp only [← Finset.sum_mul, ← Finset.mul_sum]

/-- A bounded real coefficient acts boundedly on L² pairings. -/
theorem c23_bounded_real_coefficient_pairing {d : ℕ}
    (b : Vec d → ℝ) (hb : Measurable b) (L : ℝ) (hL : 0 ≤ L)
    (hbound : ∀ x, |b x| ≤ L)
    (u v : Lp ℂ 2 (volume : Measure (Vec d))) :
    ‖∫ x, (b x : ℂ) * u x * star (v x)‖ ≤ L * ‖u‖ * ‖v‖ := by
  let w := (s5_memLp_mul hb hbound u).toLp (fun x => (b x : ℂ) * u x)
  have hw : (w : Vec d → ℂ) =ᵐ[volume] (fun x => (b x : ℂ) * u x) :=
    (s5_memLp_mul hb hbound u).coeFn_toLp
  have hnorm : ‖w‖ ≤ L * ‖u‖ := by
    rw [Lp.norm_toLp, Lp.norm_def]
    have he := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (μ := (volume : Measure (Vec d)))
      (f := fun x => (b x : ℂ) * u x) (g := (u : Vec d → ℂ)) (c := L)
      ((Complex.measurable_ofReal.comp hb).aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable u))
      (Filter.Eventually.of_forall fun x => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hbound x) (norm_nonneg _)) 2
    calc (eLpNorm (fun x => (b x : ℂ) * u x) 2 volume).toReal
        ≤ (ENNReal.ofReal L * eLpNorm (u : Vec d → ℂ) 2 volume).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top u)) he
      _ = L * (eLpNorm (u : Vec d → ℂ) 2 volume).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hL]
  have hpair : (∫ x, (b x : ℂ) * u x * star (v x)) = inner ℂ v w := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hw] with x hx
    simp only [RCLike.inner_apply, Complex.star_def]
    rw [hx]
  rw [hpair]
  calc
    ‖inner ℂ v w‖ ≤ ‖v‖ * ‖w‖ := norm_inner_le_norm _ _
    _ ≤ ‖v‖ * (L * ‖u‖) := mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
    _ = L * ‖u‖ * ‖v‖ := by ring

/-- An elliptic coefficient entry is bounded in a bilinear L² pairing. -/
theorem c23_elliptic_entry_pairing_bound {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1)
    (hsmooth : IsSmoothWithBounds M ω) (j k : Fin d) (z : Vec d)
    (u v : Lp ℂ 2 (volume : Measure (Vec d))) :
    ‖∫ x, (ω.1 (x + z) j k : ℂ) * u x * star (v x)‖ ≤ Λ * ‖u‖ * ‖v‖ := by
  apply c23_bounded_real_coefficient_pairing (fun x => ω.1 (x + z) j k)
  · exact ((hsmooth.1.1 j k).continuous.comp (continuous_id.add continuous_const)).measurable
  · exact le_trans zero_le_one hΛ
  · intro x
    exact (s5Elliptic_of_isElliptic hΛ hell (x + z)).entry_abs_le j k

/-- Pairing the transpose force with a backward quotient gives the same
translated-coefficient and coefficient-commutator decomposition. -/
theorem c23_transpose_force_quotient_pairing {d : ℕ}
    (a : Vec d → ℂ) (ha : MemLp a ∞ (volume : Measure (Vec d)))
    (f q v r : Lp ℂ 2 (volume : Measure (Vec d))) (l : Fin d) (h : ℝ)
    (hq : (q : Vec d → ℂ) =ᵐ[volume]
      (fun x => (f (x + h • unitVector l) - f x) / (h : ℂ)))
    (hr : (r : Vec d → ℂ) =ᵐ[volume]
      (fun x => (h : ℂ)⁻¹ * ((star v) (x - h • unitVector l) - (star v) x))) :
    (∫ x, f x * (a x * r x)) =
      (∫ x, a (x + h • unitVector l) * q x * star (v x)) +
      (∫ x, ((a (x + h • unitVector l) - a x) / (h : ℂ)) * f x * star (v x)) := by
  have hi := c23_principal_quotient_pairing_identity a ha f v q r l h hq hr
  convert hi using 1 <;> congr 1 <;> funext x <;> ring

/-- Each transpose force component is controlled by the quotient of the
function and the coefficient commutator. -/
theorem c23_transpose_force_component_bound {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1)
    (hsmooth : IsSmoothWithBounds M ω) (i j l : Fin d) {h : ℝ} (hh : h ≠ 0)
    (f q v r : Lp ℂ 2 (volume : Measure (Vec d)))
    (hq : (q : Vec d → ℂ) =ᵐ[volume]
      (fun x => (f (x + h • unitVector l) - f x) / (h : ℂ)))
    (hr : (r : Vec d → ℂ) =ᵐ[volume]
      (fun x => (h : ℂ)⁻¹ * ((star v) (x - h • unitVector l) - (star v) x))) :
    ‖∫ x, f x * ((ω.1 x j i : ℂ) * r x)‖ ≤
      (Λ * ‖q‖ + M 1 * ‖f‖) * ‖v‖ := by
  have ha : MemLp (fun x => (ω.1 x j i : ℂ)) ∞ volume :=
    memLp_complex_elliptic_entry volume ω.1 Λ (lt_of_lt_of_le zero_lt_one hΛ) hell
      (fun j k => (hsmooth.1.1 j k).continuous) j i
  have hi := c23_transpose_force_quotient_pairing
    (fun x => (ω.1 x j i : ℂ)) ha f q v r l h hq hr
  have hfirst := c23_elliptic_entry_pairing_bound hΛ hell hsmooth j i
    (h • unitVector l) q v
  have hsecond : ‖∫ x,
      (((ω.1 (x + h • unitVector l) j i : ℂ) - (ω.1 x j i : ℂ)) / (h : ℂ)) *
        f x * star (v x)‖ ≤ M 1 * ‖f‖ * ‖v‖ := by
    simpa only [Complex.ofReal_sub, Complex.ofReal_div] using
      c23_coefficient_quotient_pairing_bound hsmooth l j i hh f v
  rw [hi]
  calc
    ‖(∫ x, (ω.1 (x + h • unitVector l) j i : ℂ) * q x * star (v x)) +
      (∫ x, (((ω.1 (x + h • unitVector l) j i : ℂ) - (ω.1 x j i : ℂ)) /
        (h : ℂ)) * f x * star (v x))‖ ≤
      ‖∫ x, (ω.1 (x + h • unitVector l) j i : ℂ) * q x * star (v x)‖ +
      ‖∫ x, (((ω.1 (x + h • unitVector l) j i : ℂ) - (ω.1 x j i : ℂ)) /
        (h : ℂ)) * f x * star (v x)‖ := norm_add_le _ _
    _ ≤ Λ * ‖q‖ * ‖v‖ + M 1 * ‖f‖ * ‖v‖ := add_le_add hfirst hsecond
    _ = (Λ * ‖q‖ + M 1 * ‖f‖) * ‖v‖ := by ring

/-- The forward force column, paired with the backward energy test, is
controlled by the supplied gradient and the quotient gradient. -/
theorem c23_forward_force_test_bound {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1)
    (hsmooth : IsSmoothWithBounds M ω) (i l : Fin d) {h : ℝ} (hh : h ≠ 0)
    (G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    {q r : Lp ℂ 2 (volume : Measure (Vec d))}
    {Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hQ : IsPhysicalH1Graph volume (Or.inl rfl) q Q)
    (hr : (r : Vec d → ℂ) =ᵐ[volume]
      (fun x => (h : ℂ)⁻¹ * ((star q) (x - h • unitVector l) - (star q) x))) :
    ‖∫ x, (∑ j, (ω.1 x j i : ℂ) * G j x) * r x‖ ≤
      Λ * (∑ j, ‖G j‖) * ‖Q l‖ := by
  have hΛ0 : 0 ≤ Λ := le_trans zero_le_one hΛ
  have ha : ∀ j, MemLp (fun x => (ω.1 x j i : ℂ)) ∞ volume := fun j =>
    memLp_complex_elliptic_entry volume ω.1 Λ (lt_of_lt_of_le zero_lt_one hΛ) hell
      (fun j k => (hsmooth.1.1 j k).continuous) j i
  have hint : ∀ j, Integrable (fun x => (ω.1 x j i : ℂ) * G j x * r x) volume :=
    fun j => ((ha j).mul (r := 2) (Lp.memLp (G j))).integrable_mul (Lp.memLp r)
  have htest : ‖r‖ ≤ ‖Q l‖ := by
    simpa only [c23_L2_norm_star] using
      c23_backward_test_norm_le (physicalH1Graph_star q Q hQ) l h hh hr
  have hterm : ∀ j, ‖∫ x, (ω.1 x j i : ℂ) * G j x * r x‖ ≤
      Λ * ‖G j‖ * ‖r‖ := by
    intro j
    have hb := c23_elliptic_entry_pairing_bound hΛ hell hsmooth j i 0 (G j) (star r)
    have he : (∫ x, (ω.1 x j i : ℂ) * G j x * r x) =
        ∫ x, (ω.1 (x + 0) j i : ℂ) * G j x * star ((star r) x) := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_star r] with x hx
      simp only [add_zero, hx, Pi.star_apply, Complex.star_def, Complex.conj_conj]
    rw [he]
    simpa only [c23_L2_norm_star] using hb
  have heq : (∫ x, (∑ j, (ω.1 x j i : ℂ) * G j x) * r x) =
      ∑ j, ∫ x, (ω.1 x j i : ℂ) * G j x * r x := by
    calc
      (∫ x, (∑ j, (ω.1 x j i : ℂ) * G j x) * r x) =
          ∫ x, ∑ j, (ω.1 x j i : ℂ) * G j x * r x := by
            apply integral_congr_ae
            filter_upwards [] with x
            rw [Finset.sum_mul]
      _ = _ := integral_finsetSum _ (fun j _ => hint j)
  rw [heq]
  calc
    ‖∑ j, ∫ x, (ω.1 x j i : ℂ) * G j x * r x‖ ≤
        ∑ j, ‖∫ x, (ω.1 x j i : ℂ) * G j x * r x‖ := norm_sum_le _ _
    _ ≤ ∑ j, Λ * ‖G j‖ * ‖r‖ := Finset.sum_le_sum (fun j _ => hterm j)
    _ = Λ * (∑ j, ‖G j‖) * ‖r‖ := by simp only [← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ Λ * (∑ j, ‖G j‖) * ‖Q l‖ :=
      mul_le_mul_of_nonneg_left htest (mul_nonneg hΛ0 (Finset.sum_nonneg fun j _ => norm_nonneg _))

/-- The transpose force sum is bounded by the function and gradient quotients. -/
theorem c23_transpose_force_test_bound {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1)
    (hsmooth : IsSmoothWithBounds M ω) (i l : Fin d) {h : ℝ} (hh : h ≠ 0)
    (f q : Lp ℂ 2 (volume : Measure (Vec d)))
    (Q R : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hq : (q : Vec d → ℂ) =ᵐ[volume]
      (fun x => (f (x + h • unitVector l) - f x) / (h : ℂ)))
    (hR : ∀ j, (R j : Vec d → ℂ) =ᵐ[volume]
      (fun x => (h : ℂ)⁻¹ * ((star (Q j)) (x - h • unitVector l) - (star (Q j)) x))) :
    ‖∫ x, f x * (∑ j, (ω.1 x j i : ℂ) * R j x)‖ ≤
      (Λ * ‖q‖ + M 1 * ‖f‖) * (∑ j, ‖Q j‖) := by
  have ha : ∀ j, MemLp (fun x => (ω.1 x j i : ℂ)) ∞ volume := fun j =>
    memLp_complex_elliptic_entry volume ω.1 Λ (lt_of_lt_of_le zero_lt_one hΛ) hell
      (fun j k => (hsmooth.1.1 j k).continuous) j i
  have hint : ∀ j, Integrable (fun x => f x * ((ω.1 x j i : ℂ) * R j x)) volume :=
    fun j => (Lp.memLp f).integrable_mul ((ha j).mul (r := 2) (Lp.memLp (R j)))
  have heq : (∫ x, f x * (∑ j, (ω.1 x j i : ℂ) * R j x)) =
      ∑ j, ∫ x, f x * ((ω.1 x j i : ℂ) * R j x) := by
    calc
      (∫ x, f x * (∑ j, (ω.1 x j i : ℂ) * R j x)) =
          ∫ x, ∑ j, f x * ((ω.1 x j i : ℂ) * R j x) := by
            apply integral_congr_ae
            filter_upwards [] with x
            rw [Finset.mul_sum]
      _ = _ := integral_finsetSum _ (fun j _ => hint j)
  rw [heq]
  calc
    ‖∑ j, ∫ x, f x * ((ω.1 x j i : ℂ) * R j x)‖ ≤
        ∑ j, ‖∫ x, f x * ((ω.1 x j i : ℂ) * R j x)‖ := norm_sum_le _ _
    _ ≤ ∑ j, (Λ * ‖q‖ + M 1 * ‖f‖) * ‖Q j‖ := by
      apply Finset.sum_le_sum
      intro j _
      exact c23_transpose_force_component_bound hΛ hell hsmooth i j l hh f q (Q j) (R j) hq (hR j)
    _ = (Λ * ‖q‖ + M 1 * ‖f‖) * (∑ j, ‖Q j‖) := by
      rw [Finset.mul_sum]

end EinsteinFull
