import EinsteinFull.Calculus.PhysicalH1IntegrationSupport
import EinsteinRelation.Correctors.SpatialWeakProduct

/-! Smooth multipliers and weighted global integration by parts for physical H1.

Uses the actual public L2 classes and weak-gradient graph. The real smooth
product rule is reused from the pinned EinsteinRelation revision
`7748a8e9000034825873768d309be8915ae53b07`.
-/

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinFull
open EinsteinRelation

/-- A smooth bounded multiplier with bounded derivatives preserves the actual H1 graph. -/
theorem physicalH1Graph_mul_smooth {d : ℕ} (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφb : MemLp (fun x => (φ x : ℂ)) ∞ volume)
    (hDφ : ∀ j, MemLp (fun x => (coordinateDerivative j φ x : ℂ)) ∞ volume)
    (v : Lp ℂ 2 (volume : Measure (Vec d)))
    (H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hv : IsPhysicalH1Graph volume (Or.inl rfl) v H) :
    ∃ (w : Lp ℂ 2 (volume : Measure (Vec d)))
      (J : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph volume (Or.inl rfl) w J ∧
      (w : Vec d → ℂ) =ᵐ[volume] (fun x => (φ x : ℂ) * v x) ∧
      ∀ j, (J j : Vec d → ℂ) =ᵐ[volume]
        (fun x => (φ x : ℂ) * H j x + v x * (coordinateDerivative j φ x : ℂ)) := by
  have hw : MemLp (fun x => (φ x : ℂ) * v x) 2 volume := hφb.fun_mul (Lp.memLp v)
  have hJ (j : Fin d) : MemLp (fun x => (φ x : ℂ) * H j x +
      v x * (coordinateDerivative j φ x : ℂ)) 2 volume :=
    (hφb.fun_mul (Lp.memLp (H j))).add ((Lp.memLp v).fun_mul (hDφ j))
  let w := hw.toLp _
  let J (j : Fin d) := (hJ j).toLp _
  refine ⟨w, J, ?_, hw.coeFn_toLp, fun j => (hJ j).coeFn_toLp⟩
  rw [isPhysicalH1Graph_iff_representatives volume (Or.inl rfl)
    w J _ _ hw.coeFn_toLp (fun j => (hJ j).coeFn_toLp)]
  constructor
  · intro j
    simpa only [Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero] using
      Correctors.hasWeakPartialDerivative_mul_smooth isOpen_univ j (hv.1 j) hφ
  · intro j
    simpa only [Complex.mul_re, Complex.mul_im, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, zero_add, add_zero] using
      Correctors.hasWeakPartialDerivative_mul_smooth isOpen_univ j (hv.2 j) hφ

/-- Weighted global partial integration on the full physical H1 domain. -/
theorem physicalH1Graph_integral_weighted_gradient {d : ℕ} (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφb : MemLp (fun x => (φ x : ℂ)) ∞ volume)
    (hDφ : ∀ j, MemLp (fun x => (coordinateDerivative j φ x : ℂ)) ∞ volume)
    (u v : Lp ℂ 2 (volume : Measure (Vec d)))
    (G H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)))
    (hu : IsPhysicalH1Graph volume (Or.inl rfl) u G)
    (hv : IsPhysicalH1Graph volume (Or.inl rfl) v H) (j : Fin d) :
    (∫ x, G j x * (φ x : ℂ) * v x) + (∫ x, u x * (φ x : ℂ) * H j x) =
      -(∫ x, (coordinateDerivative j φ x : ℂ) * u x * v x) := by
  obtain ⟨w, J, hw, hwr, hJr⟩ := physicalH1Graph_mul_smooth φ hφ hφb hDφ v H hv
  have hibp := physicalH1Graph_integral_mul_gradient u w G J hu hw j
  have hleft : (∫ x, u x * J j x) =
      (∫ x, u x * (φ x : ℂ) * H j x) +
      (∫ x, (coordinateDerivative j φ x : ℂ) * u x * v x) := by
    have h1 : Integrable (fun x => u x * (φ x : ℂ) * H j x) volume :=
      ((Lp.memLp u).fun_mul (r := 2) hφb).integrable_mul (Lp.memLp (H j))
    have h2 : Integrable (fun x => (coordinateDerivative j φ x : ℂ) * u x * v x) volume :=
      ((hDφ j).fun_mul (r := 2) (Lp.memLp u)).integrable_mul (Lp.memLp v)
    rw [← integral_add h1 h2]
    apply integral_congr_ae
    filter_upwards [hJr j] with x hx
    rw [hx]
    ring
  have hright : (∫ x, G j x * w x) = ∫ x, G j x * (φ x : ℂ) * v x := by
    apply integral_congr_ae
    filter_upwards [hwr] with x hx
    rw [hx]
    ring
  rw [hleft, hright] at hibp
  linear_combination hibp

end EinsteinFull
