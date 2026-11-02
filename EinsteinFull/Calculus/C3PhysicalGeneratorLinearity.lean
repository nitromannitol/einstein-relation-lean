import EinsteinFull.Calculus.PhysicalComplexEvolution
import EinsteinFull.Calculus.PhysicalDomainSupport
import EinsteinRelation.Correctors.WeakPartialAddition
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.External.AKM

private theorem weakPartial_const_mul {d : ℕ} {j : Fin d}
    {f g : Vec d → ℝ} (hf : HasWeakPartialDerivative univ j f g) (c : ℝ) :
    HasWeakPartialDerivative univ j (fun x => c * f x) (fun x => c * g x) := by
  refine ⟨?_, ?_, ?_⟩
  · exact hf.1.smul c
  · exact hf.2.1.smul c
  intro φ hφ
  simp only [mul_assoc, integral_const_mul]
  rw [hf.2.2 φ hφ]
  ring

private theorem physicalH1_smul {d : ℕ} (c : ℂ)
    {u : Lp ℂ 2 (volume : Measure (Vec d))}
    {G : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hu : IsPhysicalH1Graph volume (Or.inl rfl) u G) :
    IsPhysicalH1Graph volume (Or.inl rfl) (c • u) (fun j => c • G j) := by
  rw [isPhysicalH1Graph_iff_representatives volume (Or.inl rfl)
    (c • u) (fun j => c • G j) _ _ (Lp.coeFn_smul c u)
    (fun j => Lp.coeFn_smul c (G j))]
  constructor
  · intro j
    simpa only [Pi.smul_apply, smul_eq_mul, Complex.mul_re, sub_eq_add_neg,
      neg_mul] using Correctors.hasWeakPartialDerivative_add
        (weakPartial_const_mul (hu.1 j) c.re) (weakPartial_const_mul (hu.2 j) (-c.im))
  · intro j
    simpa only [Pi.smul_apply, smul_eq_mul, Complex.mul_im] using
      Correctors.hasWeakPartialDerivative_add
        (weakPartial_const_mul (hu.2 j) c.re) (weakPartial_const_mul (hu.1 j) c.im)

private theorem physicalH1_add {d : ℕ}
    {u v : Lp ℂ 2 (volume : Measure (Vec d))}
    {G H : Fin d → Lp ℂ 2 (volume : Measure (Vec d))}
    (hu : IsPhysicalH1Graph volume (Or.inl rfl) u G)
    (hv : IsPhysicalH1Graph volume (Or.inl rfl) v H) :
    IsPhysicalH1Graph volume (Or.inl rfl) (u + v) (fun j => G j + H j) := by
  rw [isPhysicalH1Graph_iff_representatives volume (Or.inl rfl)
    (u + v) (fun j => G j + H j) _ _ (Lp.coeFn_add u v)
    (fun j => Lp.coeFn_add (G j) (H j))]
  exact ⟨fun j => by simpa only [Pi.add_apply, Complex.add_re] using
      Correctors.hasWeakPartialDerivative_add (hu.1 j) (hv.1 j),
    fun j => by simpa only [Pi.add_apply, Complex.add_im] using
      Correctors.hasWeakPartialDerivative_add (hu.2 j) (hv.2 j)⟩

private theorem linear_combination_representative {d : ℕ} (c q : ℂ)
    (u v : Lp ℂ 2 (volume : Measure (Vec d))) :
    (c • u + q • v : Lp ℂ 2 (volume : Measure (Vec d))) =ᵐ[volume]
      (fun x => c * u x + q * v x) := by
  filter_upwards [Lp.coeFn_add (c • u) (q • v), Lp.coeFn_smul c u,
    Lp.coeFn_smul q v] with x hadd hc hq
  simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
    hadd.trans (congrArg₂ (· + ·) hc hq)

/-- The literal physical weak graph is complex linear for bounded coefficients. -/
theorem physical_complex_generator_graph_linear_combination
    {d : ℕ} (a : Vec d → Mat d) (i : Fin d) (ζ c q : ℂ)
    (ha : ∀ j k, MemLp (fun x => (a x j k : ℂ)) ∞ volume)
    {u v g h : Lp ℂ 2 (volume : Measure (Vec d))}
    (hu : IsPhysicalComplexGeneratorPair a i ζ u g)
    (hv : IsPhysicalComplexGeneratorPair a i ζ v h) :
    IsPhysicalComplexGeneratorPair a i ζ (c • u+q • v) (c • g+q • h) := by
  classical
  obtain ⟨G, hG, hu⟩ := hu
  obtain ⟨H, hH, hv⟩ := hv
  refine ⟨fun j => c • G j + q • H j,
    physicalH1_add (physicalH1_smul c hG) (physicalH1_smul q hH), ?_⟩
  intro w J hw
  have hE (K : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :
      Integrable (fun x => ∑ j, ∑ k, (a x j k : ℂ) * K k x * J j x) volume := by
    apply integrable_finsetSum
    intro j _
    apply integrable_finsetSum
    intro k _
    exact ((ha j k).fun_mul (r := 2) (Lp.memLp (K k))).integrable_mul (Lp.memLp (J j))
  have hD (K : Fin d → Lp ℂ 2 (volume : Measure (Vec d))) :
      Integrable (fun x => (∑ j, (a x j i : ℂ) * K j x) * w x) volume := by
    have hsum : MemLp (fun x => ∑ j, (a x j i : ℂ) * K j x) 2 volume :=
      memLp_finsetSum _ fun j _ => (ha j i).fun_mul (r := 2) (Lp.memLp (K j))
    exact hsum.integrable_mul (Lp.memLp w)
  have heqE : (∫ x, ∑ j, ∑ k, (a x j k : ℂ) *
      (c • G k + q • H k : Lp ℂ 2 (volume : Measure (Vec d))) x * J j x) =
      c * (∫ x, ∑ j, ∑ k, (a x j k : ℂ) * G k x * J j x) +
      q * (∫ x, ∑ j, ∑ k, (a x j k : ℂ) * H k x * J j x) := by
    calc
      _ = ∫ x, c * (∑ j, ∑ k, (a x j k : ℂ) * G k x * J j x) +
          q * (∑ j, ∑ k, (a x j k : ℂ) * H k x * J j x) := by
        apply integral_congr_ae
        filter_upwards [ae_all_iff.mpr (fun k =>
          linear_combination_representative c q (G k) (H k))] with x hx
        simp only [hx, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := by rw [integral_add ((hE G).const_mul c) ((hE H).const_mul q),
        integral_const_mul, integral_const_mul]
  have heqD : (∫ x, (∑ j, (a x j i : ℂ) *
      (c • G j + q • H j : Lp ℂ 2 (volume : Measure (Vec d))) x) * w x) =
      c * (∫ x, (∑ j, (a x j i : ℂ) * G j x) * w x) +
      q * (∫ x, (∑ j, (a x j i : ℂ) * H j x) * w x) := by
    calc
      _ = ∫ x, c * ((∑ j, (a x j i : ℂ) * G j x) * w x) +
          q * ((∑ j, (a x j i : ℂ) * H j x) * w x) := by
        apply integral_congr_ae
        filter_upwards [ae_all_iff.mpr (fun j =>
          linear_combination_representative c q (G j) (H j))] with x hx
        simp only [hx, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [integral_add ((hD G).const_mul c) ((hD H).const_mul q),
        integral_const_mul, integral_const_mul]
  have heqL : (∫ x, (c • g + q • h : Lp ℂ 2 (volume : Measure (Vec d))) x * w x) =
      c * (∫ x, g x * w x) + q * (∫ x, h x * w x) := by
    calc
      _ = ∫ x, c * (g x * w x) + q * (h x * w x) := by
        apply integral_congr_ae
        filter_upwards [linear_combination_representative c q g h] with x hx
        rw [hx]
        ring
      _ = _ := by
        rw [integral_add (f := fun x => c * (g x * w x))
          (g := fun x => q * (h x * w x))
          (((Lp.memLp g).integrable_mul (Lp.memLp w)).const_mul c)
          (((Lp.memLp h).integrable_mul (Lp.memLp w)).const_mul q),
          integral_const_mul, integral_const_mul]
  rw [heqL, heqE, heqD, hu w J hw, hv w J hw]
  ring

end EinsteinFull.Blueprint
