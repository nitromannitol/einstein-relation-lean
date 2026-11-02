import EinsteinFull.Calculus.C23PhysicalGradientDifferenceEnergy

open MeasureTheory
open scoped NNReal ENNReal BigOperators Topology

namespace EinsteinFull
open EinsteinRelation

/-- The transpose energy test retains the backward quotient representatives
needed to estimate the force term. -/
theorem u4_transpose_quotient_energy_test {d : ℕ}
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
      (∀ j, (R j : Vec d → ℂ) =ᵐ[volume]
        (fun x => (h : ℂ)⁻¹ * ((star (Q j)) (x - h • unitVector l) - (star (Q j)) x))) ∧
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
  refine ⟨q, r, Q, R, hqQ, hq, hQ, hr, hR, hweak, ?_⟩
  intro j k
  exact c23_principal_quotient_pairing_identity (fun x => (a x k j : ℂ))
    (ha k j) (G k) (Q j) (Q k) (R j) l h (hQ k) (hR j)

/-- The transpose weak equation tested by the backward quotient, with its
principal and coefficient-commutator contributions separated. -/
theorem u4_transpose_split_quotient_energy {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1)
    (hsmooth : IsSmoothWithBounds M ω) {i : Fin d} {ζ : ℂ}
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    {G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ f g)
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    (l : Fin d) (h : ℝ) (hh : h ≠ 0) :
    ∃ (q r : Lp ℂ 2 (volume : Measure (Vec d)))
      (Q R : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) q Q ∧
      (q : Vec d → ℂ) =ᵐ[volume]
        (fun x => (f (x + h • unitVector l) - f x) / (h : ℂ)) ∧
      (∀ j, (Q j : Vec d → ℂ) =ᵐ[volume]
        (fun x => (G j (x + h • unitVector l) - G j x) / (h : ℂ))) ∧
      (r : Vec d → ℂ) =ᵐ[volume]
        (fun x => (h : ℂ)⁻¹ * ((star q) (x - h • unitVector l) - (star q) x)) ∧
      (∀ j, (R j : Vec d → ℂ) =ᵐ[volume]
        (fun x => (h : ℂ)⁻¹ * ((star (Q j)) (x - h • unitVector l) - (star (Q j)) x))) ∧
      (∫ x, g x * r x) =
        -(1 / 2 : ℂ) * ((∫ x, ∑ j, ∑ k,
          (ω.1 (x + h • unitVector l) k j : ℂ) * Q k x * star (Q j x)) +
          ∫ x, ∑ j, ∑ k,
          (((ω.1 (x + h • unitVector l) k j - ω.1 x k j) / h : ℝ) : ℂ) *
            G k x * star (Q j x)) +
        ζ * (∫ x, f x * (∑ j, (ω.1 x j i : ℂ) * R j x)) := by
  have ha : ∀ j k, MemLp (fun x => (ω.1 x j k : ℂ)) ∞ volume :=
    memLp_complex_elliptic_entry volume ω.1 Λ (lt_of_lt_of_le zero_lt_one hΛ) hell
      (fun j k => (hsmooth.1.1 j k).continuous)
  obtain ⟨q, r, Q, R, hqQ, hq, hQ, hr, hR, hw, hp⟩ :=
    u4_transpose_quotient_energy_test ha hfg hG l h
  have hat : ∀ j k, MemLp (fun x => (ω.1 (x + h • unitVector l) j k : ℂ)) ∞ volume := by
    intro j k
    simpa only [Function.comp_def] using
      (ha j k).comp_measurePreserving
        (measurePreserving_add_right (volume : Measure (Vec d)) (h • unitVector l))
  have hF : ∀ j k, Integrable (fun x => (ω.1 x k j : ℂ) * G k x * R j x) volume := by
    intro j k
    exact ((ha k j).mul (r := 2) (Lp.memLp (G k))).integrable_mul (Lp.memLp (R j))
  have hP : ∀ j k, Integrable (fun x =>
      (ω.1 (x + h • unitVector l) k j : ℂ) * Q k x * star (Q j x)) volume := by
    intro j k
    exact ((hat k j).mul (r := 2) (Lp.memLp (Q k))).integrable_mul (Lp.memLp (Q j)).star
  have hE : ∀ j k, Integrable (fun x =>
      (((ω.1 (x + h • unitVector l) k j - ω.1 x k j) / h : ℝ) : ℂ) *
        G k x * star (Q j x)) volume := by
    intro j k
    obtain ⟨v, hv, _⟩ := c23_coefficient_quotient_multiplier hsmooth l k j hh (G k)
    apply ((Lp.memLp v).integrable_mul (Lp.memLp (Q j)).star).congr
    filter_upwards [hv] with x hx
    simp only [Pi.mul_apply, Pi.star_apply]
    rw [hx]
  have hp' : ∀ j k, (∫ x, (ω.1 x k j : ℂ) * G k x * R j x) =
      (∫ x, (ω.1 (x + h • unitVector l) k j : ℂ) * Q k x * star (Q j x)) +
      ∫ x, (((ω.1 (x + h • unitVector l) k j - ω.1 x k j) / h : ℝ) : ℂ) *
        G k x * star (Q j x) := by
    intro j k
    simpa only [Complex.ofReal_div, Complex.ofReal_sub] using hp j k
  have hs := c23_integral_double_sum_split _ _ _ hF hP hE hp'
  refine ⟨q, r, Q, R, hqQ, hq, hQ, hr, hR, ?_⟩
  rw [hs] at hw
  exact hw

/-- Coercive energy inequality for the actual transpose quotient test. -/
theorem u4_transpose_quotient_energy_bound {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1)
    (hsmooth : IsSmoothWithBounds M ω) {i : Fin d} {ζ : ℂ}
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    {G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ f g)
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    (l : Fin d) (h : ℝ) (hh : h ≠ 0) :
    ∃ (q : Lp ℂ 2 (volume : Measure (Vec d)))
      (Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      (q : Vec d → ℂ) =ᵐ[volume]
        (fun x => (f (x + h • unitVector l) - f x) / (h : ℂ)) ∧
      (∀ j, (Q j : Vec d → ℂ) =ᵐ[volume]
        (fun x => (G j (x + h • unitVector l) - G j x) / (h : ℂ))) ∧
      Λ⁻¹ * (∑ j, ‖Q j‖ ^ 2) ≤
        2 * ‖g‖ * ‖Q l‖ + M 1 * (∑ j, ‖G j‖) * (∑ j, ‖Q j‖) +
        2 * ‖ζ‖ * (Λ * ‖q‖ + M 1 * ‖f‖) * (∑ j, ‖Q j‖) := by
  have ha : ∀ j k, MemLp (fun x => (ω.1 x j k : ℂ)) ∞ volume :=
    memLp_complex_elliptic_entry volume ω.1 Λ (lt_of_lt_of_le zero_lt_one hΛ) hell
      (fun j k => (hsmooth.1.1 j k).continuous)
  have hA : ∀ᵐ x ∂volume, S5Elliptic (ω.1 x) Λ :=
    Filter.Eventually.of_forall (s5Elliptic_of_isElliptic hΛ hell)
  obtain ⟨q, r, Q, R, hqQ, hq, hQ, hr, hR, hw⟩ :=
    u4_transpose_split_quotient_energy hΛ hell hsmooth hfg hG l h hh
  refine ⟨q, Q, hq, hQ, ?_⟩
  let P : ℂ := ∫ x, ∑ j, ∑ k,
    (ω.1 (x + h • unitVector l) k j : ℂ) * Q k x * star (Q j x)
  let E : ℂ := ∫ x, ∑ j, ∑ k,
    (((ω.1 (x + h • unitVector l) k j - ω.1 x k j) / h : ℝ) : ℂ) *
      G k x * star (Q j x)
  let T : ℂ := ∫ x, g x * r x
  let F : ℂ := ∫ x, f x * (∑ j, (ω.1 x j i : ℂ) * R j x)
  have hc : Λ⁻¹ * (∑ j, ‖Q j‖ ^ 2) ≤ P.re :=
    c23_translated_transpose_principal_coercivity ω.1 ha hA Q (h • unitVector l)
  have ht : ‖T‖ ≤ ‖g‖ * ‖Q l‖ := c23_backward_energy_forcing_bound hqQ l h hh hr
  have hf : ‖F‖ ≤ (Λ * ‖q‖ + M 1 * ‖f‖) * (∑ j, ‖Q j‖) :=
    c23_transpose_force_test_bound hΛ hell hsmooth i l hh f q Q R hq hR
  have hint : ∀ j k, Integrable (fun x =>
      (((ω.1 (x + h • unitVector l) k j - ω.1 x k j) / h : ℝ) : ℂ) *
        G k x * star (Q j x)) volume := by
    intro j k
    obtain ⟨v, hv, _⟩ := c23_coefficient_quotient_multiplier hsmooth l k j hh (G k)
    apply ((Lp.memLp v).integrable_mul (Lp.memLp (Q j)).star).congr
    filter_upwards [hv] with x hx
    simp only [Pi.mul_apply, Pi.star_apply]
    rw [hx]
  have he : ‖E‖ ≤ M 1 * (∑ j, ‖G j‖) * (∑ j, ‖Q j‖) := by
    dsimp only [E]
    rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hint j k))]
    simp_rw [integral_finsetSum _ (fun k _ => hint _ k)]
    exact c23_transpose_coefficient_quotient_sum_bound hsmooth l hh G Q
  have hid : P = -2 * T - E + 2 * ζ * F := by
    change T = -(1 / 2 : ℂ) * (P + E) + ζ * F at hw
    linear_combination 2 * hw
  have hp : ‖P‖ ≤ 2 * ‖T‖ + ‖E‖ + 2 * ‖ζ‖ * ‖F‖ := by
    rw [hid]
    calc
      ‖-2 * T - E + 2 * ζ * F‖ ≤ ‖-2 * T - E‖ + ‖2 * ζ * F‖ := norm_add_le _ _
      _ ≤ (‖-2 * T‖ + ‖E‖) + ‖2 * ζ * F‖ := by
        gcongr
        exact norm_sub_le _ _
      _ = 2 * ‖T‖ + ‖E‖ + 2 * ‖ζ‖ * ‖F‖ := by simp
  have hmul : 2 * ‖ζ‖ * ‖F‖ ≤
      2 * ‖ζ‖ * ((Λ * ‖q‖ + M 1 * ‖f‖) * (∑ j, ‖Q j‖)) :=
    mul_le_mul_of_nonneg_left hf (by positivity)
  have hre : P.re ≤ ‖P‖ := Complex.re_le_norm P
  nlinarith

/-- The forward weak equation tested by the backward quotient, with its
principal and coefficient-commutator contributions separated. -/
theorem u4_forward_split_quotient_energy {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1)
    (hsmooth : IsSmoothWithBounds M ω) {i : Fin d} {ζ : ℂ}
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    {G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexGeneratorPair ω.1 i ζ f g)
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    (l : Fin d) (h : ℝ) (hh : h ≠ 0) :
    ∃ (q r : Lp ℂ 2 (volume : Measure (Vec d)))
      (Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) q Q ∧
      (q : Vec d → ℂ) =ᵐ[volume]
        (fun x => (f (x + h • unitVector l) - f x) / (h : ℂ)) ∧
      (∀ j, (Q j : Vec d → ℂ) =ᵐ[volume]
        (fun x => (G j (x + h • unitVector l) - G j x) / (h : ℂ))) ∧
      (r : Vec d → ℂ) =ᵐ[volume]
        (fun x => (h : ℂ)⁻¹ * ((star q) (x - h • unitVector l) - (star q) x)) ∧
      (∫ x, g x * r x) =
        -(1 / 2 : ℂ) * ((∫ x, ∑ j, ∑ k,
          (ω.1 (x + h • unitVector l) j k : ℂ) * Q k x * star (Q j x)) +
          ∫ x, ∑ j, ∑ k,
          (((ω.1 (x + h • unitVector l) j k - ω.1 x j k) / h : ℝ) : ℂ) *
            G k x * star (Q j x)) +
        ζ * (∫ x, (∑ j, (ω.1 x j i : ℂ) * G j x) * r x) := by
  have ha : ∀ j k, MemLp (fun x => (ω.1 x j k : ℂ)) ∞ volume :=
    memLp_complex_elliptic_entry volume ω.1 Λ (lt_of_lt_of_le zero_lt_one hΛ) hell
      (fun j k => (hsmooth.1.1 j k).continuous)
  obtain ⟨q, r, Q, R, hqQ, hq, hQ, hr, hw, hp⟩ :=
    c23_forward_generator_quotient_energy_test ha hfg hG l h
  have hat : ∀ j k, MemLp (fun x => (ω.1 (x + h • unitVector l) j k : ℂ)) ∞ volume := by
    intro j k
    simpa only [Function.comp_def] using
      (ha j k).comp_measurePreserving
        (measurePreserving_add_right (volume : Measure (Vec d)) (h • unitVector l))
  have hF : ∀ j k, Integrable (fun x => (ω.1 x j k : ℂ) * G k x * R j x) volume := by
    intro j k
    exact ((ha j k).mul (r := 2) (Lp.memLp (G k))).integrable_mul (Lp.memLp (R j))
  have hP : ∀ j k, Integrable (fun x =>
      (ω.1 (x + h • unitVector l) j k : ℂ) * Q k x * star (Q j x)) volume := by
    intro j k
    exact ((hat j k).mul (r := 2) (Lp.memLp (Q k))).integrable_mul (Lp.memLp (Q j)).star
  have hE : ∀ j k, Integrable (fun x =>
      (((ω.1 (x + h • unitVector l) j k - ω.1 x j k) / h : ℝ) : ℂ) *
        G k x * star (Q j x)) volume := by
    intro j k
    obtain ⟨v, hv, _⟩ := c23_coefficient_quotient_multiplier hsmooth l j k hh (G k)
    apply ((Lp.memLp v).integrable_mul (Lp.memLp (Q j)).star).congr
    filter_upwards [hv] with x hx
    simp only [Pi.mul_apply, Pi.star_apply]
    rw [hx]
  have hp' : ∀ j k, (∫ x, (ω.1 x j k : ℂ) * G k x * R j x) =
      (∫ x, (ω.1 (x + h • unitVector l) j k : ℂ) * Q k x * star (Q j x)) +
      ∫ x, (((ω.1 (x + h • unitVector l) j k - ω.1 x j k) / h : ℝ) : ℂ) *
        G k x * star (Q j x) := by
    intro j k
    simpa only [Complex.ofReal_div, Complex.ofReal_sub] using hp j k
  have hs := c23_integral_double_sum_split _ _ _ hF hP hE hp'
  refine ⟨q, r, Q, hqQ, hq, hQ, hr, ?_⟩
  rw [hs] at hw
  exact hw


/-- Coercive energy inequality for the actual forward quotient test. -/
theorem u4_forward_quotient_energy_bound {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1)
    (hsmooth : IsSmoothWithBounds M ω) {i : Fin d} {ζ : ℂ}
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    {G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexGeneratorPair ω.1 i ζ f g)
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    (l : Fin d) (h : ℝ) (hh : h ≠ 0) :
    ∃ (q : Lp ℂ 2 (volume : Measure (Vec d)))
      (Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      (q : Vec d → ℂ) =ᵐ[volume]
        (fun x => (f (x + h • unitVector l) - f x) / (h : ℂ)) ∧
      (∀ j, (Q j : Vec d → ℂ) =ᵐ[volume]
        (fun x => (G j (x + h • unitVector l) - G j x) / (h : ℂ))) ∧
      Λ⁻¹ * (∑ j, ‖Q j‖ ^ 2) ≤
        2 * ‖g‖ * ‖Q l‖ + M 1 * (∑ j, ‖G j‖) * (∑ j, ‖Q j‖) +
        2 * ‖ζ‖ * (Λ * (∑ j, ‖G j‖) * ‖Q l‖) := by
  have ha : ∀ j k, MemLp (fun x => (ω.1 x j k : ℂ)) ∞ volume :=
    memLp_complex_elliptic_entry volume ω.1 Λ (lt_of_lt_of_le zero_lt_one hΛ) hell
      (fun j k => (hsmooth.1.1 j k).continuous)
  have hA : ∀ᵐ x ∂volume, S5Elliptic (ω.1 x) Λ :=
    Filter.Eventually.of_forall (s5Elliptic_of_isElliptic hΛ hell)
  obtain ⟨q, r, Q, hqQ, hq, hQ, hr, hw⟩ :=
    u4_forward_split_quotient_energy hΛ hell hsmooth hfg hG l h hh
  refine ⟨q, Q, hq, hQ, ?_⟩
  let P : ℂ := ∫ x, ∑ j, ∑ k,
    (ω.1 (x + h • unitVector l) j k : ℂ) * Q k x * star (Q j x)
  let E : ℂ := ∫ x, ∑ j, ∑ k,
    (((ω.1 (x + h • unitVector l) j k - ω.1 x j k) / h : ℝ) : ℂ) *
      G k x * star (Q j x)
  let T : ℂ := ∫ x, g x * r x
  let F : ℂ := ∫ x, (∑ j, (ω.1 x j i : ℂ) * G j x) * r x
  have hc : Λ⁻¹ * (∑ j, ‖Q j‖ ^ 2) ≤ P.re :=
    c23_translated_principal_coercivity ω.1 ha hA Q (h • unitVector l)
  have ht : ‖T‖ ≤ ‖g‖ * ‖Q l‖ := c23_backward_energy_forcing_bound hqQ l h hh hr
  have hf : ‖F‖ ≤ (Λ * (∑ j, ‖G j‖) * ‖Q l‖) :=
    c23_forward_force_test_bound hΛ hell hsmooth i l hh G hqQ hr
  have hint : ∀ j k, Integrable (fun x =>
      (((ω.1 (x + h • unitVector l) j k - ω.1 x j k) / h : ℝ) : ℂ) *
        G k x * star (Q j x)) volume := by
    intro j k
    obtain ⟨v, hv, _⟩ := c23_coefficient_quotient_multiplier hsmooth l j k hh (G k)
    apply ((Lp.memLp v).integrable_mul (Lp.memLp (Q j)).star).congr
    filter_upwards [hv] with x hx
    simp only [Pi.mul_apply, Pi.star_apply]
    rw [hx]
  have he : ‖E‖ ≤ M 1 * (∑ j, ‖G j‖) * (∑ j, ‖Q j‖) := by
    dsimp only [E]
    rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => hint j k))]
    simp_rw [integral_finsetSum _ (fun k _ => hint _ k)]
    exact c23_coefficient_quotient_sum_bound hsmooth l hh G Q
  have hid : P = -2 * T - E + 2 * ζ * F := by
    change T = -(1 / 2 : ℂ) * (P + E) + ζ * F at hw
    linear_combination 2 * hw
  have hp : ‖P‖ ≤ 2 * ‖T‖ + ‖E‖ + 2 * ‖ζ‖ * ‖F‖ := by
    rw [hid]
    calc
      ‖-2 * T - E + 2 * ζ * F‖ ≤ ‖-2 * T - E‖ + ‖2 * ζ * F‖ := norm_add_le _ _
      _ ≤ (‖-2 * T‖ + ‖E‖) + ‖2 * ζ * F‖ := by
        gcongr
        exact norm_sub_le _ _
      _ = 2 * ‖T‖ + ‖E‖ + 2 * ‖ζ‖ * ‖F‖ := by simp
  have hmul : 2 * ‖ζ‖ * ‖F‖ ≤
      2 * ‖ζ‖ * ((Λ * (∑ j, ‖G j‖) * ‖Q l‖)) :=
    mul_le_mul_of_nonneg_left hf (by positivity)
  have hre : P.re ≤ ‖P‖ := Complex.re_le_norm P
  nlinarith

/-- Both generator orientations satisfy one energy inequality with the same
supplied gradient and structural coefficients. -/
theorem u4_quotient_energy_bound {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1)
    (hsmooth : IsSmoothWithBounds M ω) {i : Fin d} {ζ : ℂ}
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    {G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexGeneratorPair ω.1 i ζ f g ∨
      IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ f g)
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    (l : Fin d) (h : ℝ) (hh : h ≠ 0) :
    ∃ (Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      (∀ j, (Q j : Vec d → ℂ) =ᵐ[volume]
        (fun x => (G j (x + h • unitVector l) - G j x) / (h : ℂ))) ∧
      Λ⁻¹ * (∑ j, ‖Q j‖ ^ 2) ≤
        2 * ‖g‖ * (∑ j, ‖Q j‖) + M 1 * (∑ j, ‖G j‖) * (∑ j, ‖Q j‖) +
        2 * ‖ζ‖ * (Λ * (∑ j, ‖G j‖) + M 1 * ‖f‖) * (∑ j, ‖Q j‖) := by
  have hM : 0 ≤ M 1 := (c18_smooth_coefficient_divergence_bounds hsmooth).1
  have hΛ0 : 0 ≤ Λ := le_trans zero_le_one hΛ
  have hsum (U : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :
      ‖U l‖ ≤ ∑ j, ‖U j‖ :=
    Finset.single_le_sum (fun j _ => norm_nonneg (U j)) (Finset.mem_univ l)
  have hGsum : 0 ≤ ∑ j, ‖G j‖ := Finset.sum_nonneg (fun j _ => norm_nonneg _)
  rcases hfg with hf | hf
  · obtain ⟨q, Q, hq, hQ, hb⟩ :=
      u4_forward_quotient_energy_bound hΛ hell hsmooth hf hG l h hh
    refine ⟨Q, hQ, ?_⟩
    have hQsum : 0 ≤ ∑ j, ‖Q j‖ := Finset.sum_nonneg (fun j _ => norm_nonneg _)
    have hforce : Λ * (∑ j, ‖G j‖) * ‖Q l‖ ≤
        (Λ * (∑ j, ‖G j‖) + M 1 * ‖f‖) * (∑ j, ‖Q j‖) := by
      gcongr
      · nlinarith [mul_nonneg hM (norm_nonneg f)]
      · exact hsum Q
    have hg : 2 * ‖g‖ * ‖Q l‖ ≤ 2 * ‖g‖ * (∑ j, ‖Q j‖) := by
      gcongr
      exact hsum Q
    have hz := mul_le_mul_of_nonneg_left hforce (show 0 ≤ 2 * ‖ζ‖ by positivity)
    nlinarith
  · obtain ⟨q, Q, hq, hQ, hb⟩ :=
      u4_transpose_quotient_energy_bound hΛ hell hsmooth hf hG l h hh
    refine ⟨Q, hQ, ?_⟩
    have hQsum : 0 ≤ ∑ j, ‖Q j‖ := Finset.sum_nonneg (fun j _ => norm_nonneg _)
    have hqbound : ‖q‖ ≤ ∑ j, ‖G j‖ :=
      le_trans (c23_forward_difference_quotient_norm_le hG l h hh hq) (hsum G)
    have hforce : (Λ * ‖q‖ + M 1 * ‖f‖) * (∑ j, ‖Q j‖) ≤
        (Λ * (∑ j, ‖G j‖) + M 1 * ‖f‖) * (∑ j, ‖Q j‖) := by
      gcongr
    have hg : 2 * ‖g‖ * ‖Q l‖ ≤ 2 * ‖g‖ * (∑ j, ‖Q j‖) := by
      gcongr
      exact hsum Q
    have hz := mul_le_mul_of_nonneg_left hforce (show 0 ≤ 2 * ‖ζ‖ by positivity)
    nlinarith

/-- The quotient energy inequality after absorbing its linear quotient term. -/
theorem u4_absorbed_quotient_energy_bound {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    {ω : FieldPair d} (hΛ : 1 ≤ Λ) (hell : IsElliptic Λ ω.1)
    (hsmooth : IsSmoothWithBounds M ω) {i : Fin d} {ζ : ℂ}
    {f g : Lp ℂ 2 (volume : Measure (Vec d))}
    {G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hfg : IsPhysicalComplexGeneratorPair ω.1 i ζ f g ∨
      IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ f g)
    (hG : IsPhysicalH1Graph volume (Or.inl rfl) f G)
    (l : Fin d) (h : ℝ) (hh : h ≠ 0) :
    ∃ (Q : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      (∀ j, (Q j : Vec d → ℂ) =ᵐ[volume]
        (fun x => (G j (x + h • unitVector l) - G j x) / (h : ℂ))) ∧
      (∑ j, ‖Q j‖ ^ 2) ≤ (Λ * (d : ℝ)) ^ 2 *
        (2 * ‖g‖ + M 1 * (∑ j, ‖G j‖) +
          2 * ‖ζ‖ * (Λ * (∑ j, ‖G j‖) + M 1 * ‖f‖)) ^ 2 := by
  obtain ⟨Q, hQ, hb⟩ := u4_quotient_energy_bound hΛ hell hsmooth hfg hG l h hh
  refine ⟨Q, hQ, ?_⟩
  let S : ℝ := ∑ j, ‖Q j‖
  let K : ℝ := 2 * ‖g‖ + M 1 * (∑ j, ‖G j‖) +
    2 * ‖ζ‖ * (Λ * (∑ j, ‖G j‖) + M 1 * ‖f‖)
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have hinv : 0 ≤ Λ⁻¹ := inv_nonneg.mpr hΛpos.le
  have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg d
  have hs : S ^ 2 ≤ (d : ℝ) * ∑ j, ‖Q j‖ ^ 2 := c23_sum_L2_norm_sq_le Q
  have he : Λ⁻¹ * S ^ 2 ≤ (d : ℝ) * S * K := by
    have h1 := mul_le_mul_of_nonneg_left hs hinv
    have h2 := mul_le_mul_of_nonneg_left hb hd
    dsimp only [S, K] at h1 ⊢
    nlinarith
  have habs := c23_absorb_quadratic_energy Λ⁻¹ (d : ℝ) 0 S K hinv (by simpa using he)
  have hinv' : Λ ^ 2 * Λ⁻¹ ^ 2 = 1 := by
    field_simp [ne_of_gt hΛpos]
  have hscale := mul_le_mul_of_nonneg_left habs (sq_nonneg Λ)
  have hsq : (∑ j, ‖Q j‖ ^ 2) ≤ S ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ => norm_nonneg (Q j))
  calc
    (∑ j, ‖Q j‖ ^ 2) ≤ S ^ 2 := hsq
    _ = Λ ^ 2 * (Λ⁻¹ ^ 2 * S ^ 2) := by rw [← mul_assoc, hinv', one_mul]
    _ ≤ Λ ^ 2 * (((d : ℝ) ^ 2 + 2 * Λ⁻¹ * 0) * K ^ 2) := hscale
    _ = (Λ * (d : ℝ)) ^ 2 * K ^ 2 := by ring

/-- Uniform L² bounds for the physical gradient difference quotients. -/
theorem c23_physical_gradient_difference_quotient_bound {d : ℕ} {Λ : ℝ} {M : ℕ → ℝ}
    (hΛ : 1 ≤ Λ) (i : Fin d) (ζ : ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ω : FieldPair d),
      IsElliptic Λ ω.1 → IsSmoothWithBounds M ω →
      ∀ f g : Lp ℂ 2 (volume : Measure (Vec d)),
      (IsPhysicalComplexGeneratorPair ω.1 i ζ f g ∨
        IsPhysicalComplexTransposeGeneratorPair ω.1 i ζ f g) →
      ∀ G : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
      IsPhysicalH1Graph volume (Or.inl rfl) f G →
      ∀ (l : Fin d) (h : ℝ), 0 < |h| → |h| ≤ 1 →
      (∀ j, MemLp (fun x => (G j (x + h • unitVector l) - G j x) / (h : ℂ))
        2 (volume : Measure (Vec d))) ∧
      (∑ j : Fin d, ((eLpNorm (fun x =>
        (G j (x + h • unitVector l) - G j x) / (h : ℂ))
        2 (volume : Measure (Vec d))).toReal)^2) ≤ C * (‖f‖^2 + ‖g‖^2) := by
  let A : ℝ := 4 * Λ + 4 * ((d : ℝ) + 1)^2 * Λ^4 * ‖ζ‖^2
  let U : ℝ := M 1 + 2 * ‖ζ‖ * Λ
  let V : ℝ := 2 * ‖ζ‖ * M 1
  let C : ℝ := 1 + (Λ * (d : ℝ))^2 * 3 * (4 + U^2 * (d : ℝ) * A + V^2)
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro ω hell hsmooth f g hfg G hG l h hh _
  have hh0 : h ≠ 0 := abs_pos.mp hh
  refine ⟨fun j => c18_L2_coordinate_difference_quotient_memLp (G j) l h, ?_⟩
  have ha : ∀ j k, MemLp (fun x => (ω.1 x j k : ℂ)) ∞ volume :=
    memLp_complex_elliptic_entry volume ω.1 Λ hΛpos hell
      (fun j k => (hsmooth.1.1 j k).continuous)
  have hAell : ∀ᵐ x ∂volume, S5Elliptic (ω.1 x) Λ :=
    Filter.Eventually.of_forall (s5Elliptic_of_isElliptic hΛ hell)
  obtain ⟨Q, hQ, henergy⟩ := u4_absorbed_quotient_energy_bound hΛ hell hsmooth hfg hG l h hh0
  have hrewrite : (∑ j : Fin d, ((eLpNorm (fun x =>
      (G j (x + h • unitVector l) - G j x) / (h : ℂ))
      2 (volume : Measure (Vec d))).toReal)^2) = ∑ j, ‖Q j‖^2 := by
    apply Finset.sum_congr rfl
    intro j _
    rw [← eLpNorm_congr_ae (hQ j), ← Lp.norm_def]
  rw [hrewrite]
  let B : ℝ := ‖f‖^2 + ‖g‖^2
  let T : ℝ := ∑ j, ‖G j‖
  let K : ℝ := 2 * ‖g‖ + M 1 * T + 2 * ‖ζ‖ * (Λ * T + M 1 * ‖f‖)
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hfB : ‖f‖^2 ≤ B := by dsimp [B]; nlinarith [sq_nonneg ‖g‖]
  have hgB : ‖g‖^2 ≤ B := by dsimp [B]; nlinarith [sq_nonneg ‖f‖]
  have hfgB : ‖f‖ * ‖g‖ ≤ B := by
    dsimp [B]
    nlinarith [sq_nonneg (‖f‖ - ‖g‖)]
  have hgrad := c23_supplied_gradient_graph_bound ω.1 i ζ ha hΛpos hAell hfg hG
  have hgrad' : (∑ j, ‖G j‖^2) ≤ A * B := by
    calc
      (∑ j, ‖G j‖^2) ≤ 4 * Λ * ‖f‖ * ‖g‖ +
          4 * ((d : ℝ) + 1)^2 * Λ^4 * ‖ζ‖^2 * ‖f‖^2 := hgrad
      _ ≤ 4 * Λ * B + 4 * ((d : ℝ) + 1)^2 * Λ^4 * ‖ζ‖^2 * B := by
        apply add_le_add
        · simpa only [mul_assoc] using
            mul_le_mul_of_nonneg_left hfgB (show 0 ≤ 4 * Λ by positivity)
        · exact mul_le_mul_of_nonneg_left hfB (by positivity)
      _ = A * B := by dsimp [A]; ring
  have hT : T^2 ≤ (d : ℝ) * A * B := by
    calc
      T^2 ≤ (d : ℝ) * ∑ j, ‖G j‖^2 := c23_sum_L2_norm_sq_le G
      _ ≤ (d : ℝ) * (A * B) := mul_le_mul_of_nonneg_left hgrad' (Nat.cast_nonneg d)
      _ = (d : ℝ) * A * B := by ring
  have hK : K^2 ≤ 3 * (4 * ‖g‖^2 + U^2 * T^2 + V^2 * ‖f‖^2) := by
    dsimp [K, U, V]
    nlinarith [sq_nonneg (2 * ‖g‖ - (M 1 + 2 * ‖ζ‖ * Λ) * T),
      sq_nonneg (2 * ‖g‖ - (2 * ‖ζ‖ * M 1) * ‖f‖),
      sq_nonneg ((M 1 + 2 * ‖ζ‖ * Λ) * T - (2 * ‖ζ‖ * M 1) * ‖f‖)]
  have hK' : K^2 ≤ 3 * (4 + U^2 * (d : ℝ) * A + V^2) * B := by
    calc
      K^2 ≤ 3 * (4 * ‖g‖^2 + U^2 * T^2 + V^2 * ‖f‖^2) := hK
      _ ≤ 3 * (4 * B + U^2 * ((d : ℝ) * A * B) + V^2 * B) := by
        gcongr
      _ = 3 * (4 + U^2 * (d : ℝ) * A + V^2) * B := by ring
  have hlast := mul_le_mul_of_nonneg_left hK' (sq_nonneg (Λ * (d : ℝ)))
  change (∑ j, ‖Q j‖^2) ≤ C * B
  change (∑ j, ‖Q j‖^2) ≤ (Λ * (d : ℝ))^2 * K^2 at henergy
  dsimp only [C]
  nlinarith

end EinsteinFull

