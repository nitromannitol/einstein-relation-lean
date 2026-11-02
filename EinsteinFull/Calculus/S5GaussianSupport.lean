import EinsteinFull.Calculus.S5LimitSupport
import EinsteinRelation.TimeChange.EuclideanTransport

/-!
# Gaussian separation from the weighted estimate

From the exponential-weight bound for every real `q` and every Euclidean-`1`-Lipschitz `ψ`,
choose `ψ` the Euclidean distance to the source set `E` and `q = ℓ / (2 C t)`.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace EinsteinFull
open EinsteinRelation

section S5Gaussian

variable {d : ℕ}

theorem s5_euclid_nonneg (v : Vec d) : 0 ≤ euclideanNorm v := Real.sqrt_nonneg _

theorem s5_euclid_symm (a b : Vec d) : euclideanNorm (a - b) = euclideanNorm (b - a) := by
  have h := TimeChange.euclideanNorm_smul (-1 : ℝ) (a - b)
  rw [neg_one_smul, neg_sub, abs_neg, abs_one, one_mul] at h
  exact h.symm

theorem s5_euclid_zero : euclideanNorm (0 : Vec d) = 0 := by
  simp [euclideanNorm, euclideanSq, dot]

/-- Euclidean distance to a set. -/
def s5DistTo (E : Set (Vec d)) (x : Vec d) : ℝ := ⨅ y : E, euclideanNorm (x - (y : Vec d))

theorem s5DistTo_bdd (E : Set (Vec d)) (x : Vec d) :
    BddBelow (Set.range fun y : E => euclideanNorm (x - (y : Vec d))) :=
  ⟨0, by
    rintro _ ⟨y, rfl⟩
    exact s5_euclid_nonneg _⟩

theorem s5DistTo_nonneg (E : Set (Vec d)) (x : Vec d) : 0 ≤ s5DistTo E x :=
  Real.iInf_nonneg fun _ => s5_euclid_nonneg _

theorem s5DistTo_le {E : Set (Vec d)} (hE : E.Nonempty) (x z : Vec d) :
    s5DistTo E x ≤ s5DistTo E z + euclideanNorm (x - z) := by
  haveI : Nonempty E := hE.to_subtype
  have h0 : s5DistTo E x - euclideanNorm (x - z) ≤ s5DistTo E z := by
    refine le_ciInf fun y => ?_
    have h1 : s5DistTo E x ≤ euclideanNorm (x - (y : Vec d)) := ciInf_le (s5DistTo_bdd E x) y
    have h2 : euclideanNorm (x - (y : Vec d)) ≤
        euclideanNorm (x - z) + euclideanNorm (z - (y : Vec d)) := by
      have := TimeChange.euclideanNorm_add_le (x - z) (z - (y : Vec d))
      rwa [sub_add_sub_cancel] at this
    linarith
  linarith

theorem s5DistTo_lip {E : Set (Vec d)} (hE : E.Nonempty) :
    ∀ x y, |s5DistTo E x - s5DistTo E y| ≤ euclideanNorm (x - y) := by
  intro x y
  rw [abs_le]
  constructor
  · have := s5DistTo_le hE y x
    rw [s5_euclid_symm y x] at this
    linarith
  · have := s5DistTo_le hE x y
    linarith

theorem s5DistTo_zero_of_mem {E : Set (Vec d)} {x : Vec d} (hx : x ∈ E) : s5DistTo E x = 0 := by
  apply le_antisymm
  · have h := ciInf_le (s5DistTo_bdd E x) (⟨x, hx⟩ : E)
    simp only [sub_self, s5_euclid_zero] at h
    exact h
  · exact s5DistTo_nonneg E x

theorem s5DistTo_ge {E : Set (Vec d)} (hE : E.Nonempty) {F : Set (Vec d)} {ℓ : ℝ}
    (hsep : ∀ x ∈ E, ∀ y ∈ F, ℓ ≤ euclideanNorm (x - y)) :
    ∀ y ∈ F, ℓ ≤ s5DistTo E y := by
  intro y hy
  haveI : Nonempty E := hE.to_subtype
  refine le_ciInf fun x => ?_
  rw [s5_euclid_symm]
  exact hsep x x.2 y hy

theorem s5_gaussian_of_weighted {C t ζn : ℝ} (hC : 0 < C) (ht : 0 < t)
    (S : Lp ℂ 2 (volume : Measure (Vec d)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec d)))
    (Hw : ∀ (q : ℝ) (ψ : Vec d → ℝ), (∀ x y, |ψ x - ψ y| ≤ euclideanNorm (x - y)) →
      ∀ f : Lp ℂ 2 (volume : Measure (Vec d)),
        MemLp (fun x => ((Real.exp (q * ψ x) : ℝ) : ℂ) * f x) 2 volume →
        MemLp (fun x => ((Real.exp (q * ψ x) : ℝ) : ℂ) * (S f) x) 2 volume ∧
          (eLpNorm (fun x => ((Real.exp (q * ψ x) : ℝ) : ℂ) * (S f) x) 2 volume).toReal ≤
            Real.exp (C * (ζn ^ 2 + q ^ 2) * t) *
              (eLpNorm (fun x => ((Real.exp (q * ψ x) : ℝ) : ℂ) * f x) 2 volume).toReal)
    (E F : Set (Vec d)) (hF : MeasurableSet F) (ℓ : ℝ) (hℓ : 0 ≤ ℓ)
    (hsep : ∀ x ∈ E, ∀ y ∈ F, ℓ ≤ euclideanNorm (x - y))
    (f : Lp ℂ 2 (volume : Measure (Vec d)))
    (hf0 : ∀ᵐ x ∂(volume : Measure (Vec d)), x ∉ E → f x = 0) :
    MemLp (F.indicator (fun x => (S f) x)) 2 volume ∧
      (eLpNorm (F.indicator (fun x => (S f) x)) 2 volume).toReal ≤
        Real.exp (C * ζn ^ 2 * t - (1 / (4 * C)) * ℓ ^ 2 / t) * ‖f‖ := by
  by_cases hE : E.Nonempty
  · set q : ℝ := ℓ / (2 * C * t) with hq
    have hq0 : 0 ≤ q := by positivity
    have hψL := s5DistTo_lip hE
    have hef : (fun x => ((Real.exp (q * s5DistTo E x) : ℝ) : ℂ) * f x) =ᵐ[volume]
        fun x => f x := by
      filter_upwards [hf0] with x hx
      by_cases hxE : x ∈ E
      · simp [s5DistTo_zero_of_mem hxE]
      · simp [hx hxE]
    have hfm : MemLp (fun x => ((Real.exp (q * s5DistTo E x) : ℝ) : ℂ) * f x) 2 volume :=
      (Lp.memLp f).ae_eq hef.symm
    obtain ⟨hm, hn⟩ := Hw q (s5DistTo E) hψL f hfm
    rw [eLpNorm_congr_ae hef, ← Lp.norm_def f] at hn
    have hpt : ∀ y, ‖F.indicator (fun x => (S f) x) y‖ ≤
        Real.exp (-(q * ℓ)) * ‖((Real.exp (q * s5DistTo E y) : ℝ) : ℂ) * (S f) y‖ := by
      intro y
      by_cases hy : y ∈ F
      · rw [Set.indicator_of_mem hy, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _)]
        have h1 : Real.exp (q * ℓ) ≤ Real.exp (q * s5DistTo E y) :=
          Real.exp_le_exp.2
            (mul_le_mul_of_nonneg_left (s5DistTo_ge hE hsep y hy) hq0)
        calc ‖(S f) y‖ = Real.exp (-(q * ℓ)) * (Real.exp (q * ℓ) * ‖(S f) y‖) := by
              rw [← mul_assoc, ← Real.exp_add]
              simp
          _ ≤ _ := by gcongr
      · rw [Set.indicator_of_notMem hy, norm_zero]
        positivity
    have hint : AEStronglyMeasurable (F.indicator fun x => (S f) x) volume :=
      (Lp.aestronglyMeasurable (S f)).indicator hF
    have hle := eLpNorm_le_mul_eLpNorm_of_ae_le_mul hint (Filter.Eventually.of_forall hpt) 2
    have hmem : MemLp (F.indicator fun x => (S f) x) 2 volume :=
      hle.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hm.eLpNorm_lt_top)
    refine ⟨hmem, ?_⟩
    have h2 := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hm.eLpNorm_lt_top.ne) hle
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at h2
    have h3 : Real.exp (-(q * ℓ)) * Real.exp (C * (ζn ^ 2 + q ^ 2) * t) =
        Real.exp (C * ζn ^ 2 * t - (1 / (4 * C)) * ℓ ^ 2 / t) := by
      rw [← Real.exp_add]
      congr 1
      rw [hq]
      field_simp
      ring
    calc _ ≤ _ := h2
      _ ≤ Real.exp (-(q * ℓ)) * (Real.exp (C * (ζn ^ 2 + q ^ 2) * t) * ‖f‖) :=
        mul_le_mul_of_nonneg_left hn (Real.exp_pos _).le
      _ = _ := by rw [← mul_assoc, h3]
  · have hE' : E = ∅ := Set.not_nonempty_iff_eq_empty.mp hE
    have hf : f = 0 := by
      apply Lp.ext
      filter_upwards [hf0, Lp.coeFn_zero ℂ 2 (volume : Measure (Vec d))] with x hx h0
      rw [h0]
      exact hx (by simp [hE'])
    subst hf
    rw [map_zero]
    have hmem : MemLp (F.indicator fun x => ((0 : Lp ℂ 2 (volume : Measure (Vec d))) : Vec d → ℂ) x)
        2 volume := (Lp.memLp (0 : Lp ℂ 2 (volume : Measure (Vec d)))).indicator hF
    refine ⟨hmem, ?_⟩
    have h1 : eLpNorm (F.indicator fun x => ((0 : Lp ℂ 2 (volume : Measure (Vec d))) :
        Vec d → ℂ) x) 2 volume = 0 := by
      refine le_antisymm ?_ zero_le
      refine (eLpNorm_indicator_le _ hF).trans (le_of_eq ?_)
      rw [eLpNorm_congr_ae (Lp.coeFn_zero ℂ 2 (volume : Measure (Vec d)))]
      simp
    rw [h1]
    simp

end S5Gaussian

end EinsteinFull
