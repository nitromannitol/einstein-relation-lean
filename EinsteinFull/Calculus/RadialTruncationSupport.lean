import EinsteinFull.Calculus.ComplexRadialEnergySupport
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Smooth bounded radial weights for stationary Lp tests

For positive `ε,R`, the weight `(ε + R*s/(R+s))^a` increases on `s ≥ 0`
and is bounded by `(ε+R)^a` for `a ≥ 0`. Its logarithmic slope is at most
`a`. Thus the associated complex radial tests have bounded differentials,
uniformly controlled relative to their weights, as required by both the
forward and transpose energy estimates.
-/

open MeasureTheory Filter
open EinsteinRelation
open scoped NNReal Topology

noncomputable section

namespace EinsteinFull

/-- A smooth saturation of the squared radial variable on the nonnegative half-line. -/
def radialTruncationBase (ε R s : ℝ) : ℝ := ε + R * s / (R + s)

/-- The bounded power weight for a radial test of exponent `p = 2+2a`. -/
def radialTruncationWeight (ε R a s : ℝ) : ℝ := (radialTruncationBase ε R s) ^ a

/-- The literal derivative of the bounded power weight on the nonnegative half-line. -/
def radialTruncationSlope (ε R a s : ℝ) : ℝ :=
  a * (radialTruncationBase ε R s) ^ (a - 1) * R ^ 2 / (R + s) ^ 2

/-- The saturated radial variable is positive and bounded by its cutoff. -/
theorem radialTruncationBase_pos_le {ε R s : ℝ} (hε : 0 < ε) (hR : 0 < R)
    (hs : 0 ≤ s) :
    0 < radialTruncationBase ε R s ∧ radialTruncationBase ε R s ≤ ε + R := by
  have hden : 0 < R + s := add_pos_of_pos_of_nonneg hR hs
  constructor
  · exact add_pos_of_pos_of_nonneg hε (div_nonneg (mul_nonneg hR.le hs) hden.le)
  · unfold radialTruncationBase
    apply add_le_add_right
    apply (div_le_iff₀ hden).mpr
    nlinarith only [sq_nonneg R]

/-- The radial power weight has its exact derivative at every nonnegative argument. -/
theorem hasDerivAt_radialTruncationWeight {ε R a s : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (hs : 0 ≤ s) :
    HasDerivAt (radialTruncationWeight ε R a) (radialTruncationSlope ε R a s) s := by
  have hden : R + s ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg hR hs)
  have hb : HasDerivAt (radialTruncationBase ε R)
      (R ^ 2 / (R + s) ^ 2) s := by
    unfold radialTruncationBase
    convert ((((hasDerivAt_id s).const_mul R).div
      ((hasDerivAt_id s).const_add R) hden).const_add ε) using 1
    · rfl
    · simp only [id_eq, mul_one]
      ring
  have h := hb.rpow_const (p := a) (Or.inl (radialTruncationBase_pos_le hε hR hs).1.ne')
  unfold radialTruncationWeight
  apply h.congr_deriv
  unfold radialTruncationSlope
  ring

/-- Saturation bounds the derivative multiplied by the squared radial variable. -/
theorem radialTruncationSlope_mul_le {ε R a s : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (ha : 0 ≤ a) (hs : 0 ≤ s) :
    0 ≤ radialTruncationSlope ε R a s ∧
      radialTruncationSlope ε R a s * s ≤ a * radialTruncationWeight ε R a s := by
  have hb := (radialTruncationBase_pos_le hε hR hs).1
  have hden : 0 < R + s := add_pos_of_pos_of_nonneg hR hs
  have hrat : s * R ^ 2 / (R + s) ^ 2 ≤ R * s / (R + s) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hden) hden).mpr
    have hpos : 0 ≤ R * s ^ 2 := mul_nonneg hR.le (sq_nonneg s)
    nlinarith only [mul_nonneg hden.le hpos]
  have hsmall : s * R ^ 2 / (R + s) ^ 2 ≤ radialTruncationBase ε R s :=
    hrat.trans (le_add_of_nonneg_left hε.le)
  constructor
  · unfold radialTruncationSlope
    positivity
  · calc
      radialTruncationSlope ε R a s * s =
          a * (radialTruncationBase ε R s) ^ (a - 1) *
            (s * R ^ 2 / (R + s) ^ 2) := by unfold radialTruncationSlope; ring
      _ ≤ a * (radialTruncationBase ε R s) ^ (a - 1) *
          radialTruncationBase ε R s :=
        mul_le_mul_of_nonneg_left hsmall
          (mul_nonneg ha (Real.rpow_nonneg hb.le _))
      _ = a * radialTruncationWeight ε R a s := by
        rw [Real.rpow_sub_one hb.ne']
        unfold radialTruncationWeight
        field_simp

/-- A uniform differential bound for the bounded radial power weight. -/
theorem radialTruncationWeight_differential_bound {ε R a s : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (ha : 0 ≤ a) (hs : 0 ≤ s) :
    |radialTruncationWeight ε R a s| + 2 * |radialTruncationSlope ε R a s| * s ≤
      (1 + 2 * a) * (ε + R) ^ a := by
  have hb := radialTruncationBase_pos_le hε hR hs
  have hd := radialTruncationSlope_mul_le hε hR ha hs
  have hw : 0 ≤ radialTruncationWeight ε R a s := Real.rpow_nonneg hb.1.le _
  rw [abs_of_nonneg hw, abs_of_nonneg hd.1]
  calc
    _ ≤ (1 + 2 * a) * radialTruncationWeight ε R a s := by
      nlinarith only [hd.2]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hb.1.le hb.2 ha)
      (by positivity)

/-- Both the bounded weight and its slope are continuous on the squared-radius domain. -/
theorem continuousOn_radialTruncationWeight_slope {ε R a : ℝ}
    (hε : 0 < ε) (hR : 0 < R) :
    ContinuousOn (radialTruncationWeight ε R a) (Set.Ici 0) ∧
      ContinuousOn (radialTruncationSlope ε R a) (Set.Ici 0) := by
  have hden (s : ℝ) (hs : s ∈ Set.Ici (0 : ℝ)) : R + s ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg hR hs)
  have hb : ContinuousOn (radialTruncationBase ε R) (Set.Ici 0) :=
    continuousOn_const.add ((continuousOn_const.mul continuousOn_id).div
      (continuousOn_const.add continuousOn_id) hden)
  have hpos (s : ℝ) (hs : s ∈ Set.Ici (0 : ℝ)) :
      radialTruncationBase ε R s ≠ 0 := (radialTruncationBase_pos_le hε hR hs).1.ne'
  constructor
  · exact hb.rpow_const (fun s hs => Or.inl (hpos s hs))
  · exact ((continuousOn_const.mul
      (hb.rpow_const (p := a - 1) (fun s hs => Or.inl (hpos s hs)))).mul
        continuousOn_const).div ((continuousOn_const.add continuousOn_id).pow 2)
          (fun s hs => pow_ne_zero 2 (hden s hs))

/-- The concrete bounded radial power test is globally Lipschitz, with an explicit cutoff bound. -/
theorem lipschitzWith_radialTruncation {ε R a : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (ha : 0 ≤ a) :
    LipschitzWith ⟨(1 + 2 * a) * (ε + R) ^ a, by positivity⟩
      (fun z : ℂ => radialTruncationWeight ε R a (‖z‖ ^ 2) • z) :=
  lipschitzWith_complexRadial
    (fun _ hs => hasDerivAt_radialTruncationWeight hε hR hs)
    (fun _ hs => radialTruncationWeight_differential_bound hε hR ha hs)

/-- The concrete radial truncation is admissible on the full actual stationary H1 domain. -/
theorem HasComplexHorizontalGradient.radialTruncation {d : ℕ} {Q : Measure (FieldPair d)}
    {hQ : IsStationary Q} {f : Lp ℂ 2 Q} {G : Fin d → Lp ℂ 2 Q}
    (hf : HasComplexHorizontalGradient Q hQ f G) {ε R a : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (ha : 0 ≤ a) :
    let hLip := lipschitzWith_radialTruncation hε hR ha
    let hzero : (fun z : ℂ => radialTruncationWeight ε R a (‖z‖ ^ 2) • z) 0 = 0 :=
      by simp only [smul_zero]
    ∃ H : Fin d → Lp ℂ 2 Q,
      HasComplexHorizontalGradient Q hQ (hLip.compLp hzero f) H ∧
        (∀ j : Fin d, H j =ᵐ[Q] fun ω =>
          complexRadialDifferential (radialTruncationWeight ε R a (‖f ω‖ ^ 2))
            (radialTruncationSlope ε R a (‖f ω‖ ^ 2)) (f ω) (G j ω)) := by
  obtain ⟨hc, hd⟩ := continuousOn_radialTruncationWeight_slope (a := a) hε hR
  exact hf.comp_radial (K := ⟨(1 + 2 * a) * (ε + R) ^ a, by positivity⟩) hc hd (fun _ hs => hasDerivAt_radialTruncationWeight hε hR hs)
    (fun _ hs => radialTruncationWeight_differential_bound hε hR ha hs)

/-- Sending the squared cutoff to infinity recovers the regularized power weight. -/
theorem tendsto_radialTruncationWeight_atTop {ε s a : ℝ}
    (hε : 0 < ε) (hs : 0 ≤ s) :
    Tendsto (fun R : ℝ => radialTruncationWeight ε R a s) atTop (𝓝 ((ε + s) ^ a)) := by
  have hi : Tendsto (fun R : ℝ => s / R) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hb : Tendsto (fun R : ℝ => ε + s / (1 + s / R)) atTop (𝓝 (ε + s)) := by
    convert tendsto_const_nhds.add
      (tendsto_const_nhds.div (tendsto_const_nhds.add hi) (by norm_num : (1 : ℝ) + 0 ≠ 0))
      using 1
    simp only [add_zero, div_one]
  have hw := (Real.continuousAt_rpow_const (ε + s) a
    (Or.inl (add_pos_of_pos_of_nonneg hε hs).ne')).tendsto.comp hb
  apply hw.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  unfold radialTruncationWeight radialTruncationBase
  change (ε + s / (1 + s / R)) ^ a = (ε + R * s / (R + s)) ^ a
  congr 1
  field_simp

/-- Removing the positive regularization recovers the power at every squared radius. -/
theorem tendsto_regularizedRadialWeight {s a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun ε : ℝ => (ε + s) ^ a) (𝓝 0) (𝓝 (s ^ a)) := by
  have hc : ContinuousAt (fun ε : ℝ => ε + s) 0 := continuousAt_id.add continuousAt_const
  have h := hc.rpow_const (p := a) (Or.inr ha)
  simpa only [id_eq, zero_add] using h.tendsto

/-- The concrete transpose test gradient has a cutoff-independent relative norm bound. -/
theorem norm_radialTruncationDifferential_le {ε R a : ℝ}
    (hε : 0 < ε) (hR : 0 < R) (ha : 0 ≤ a) (z : ℂ) :
    ‖complexRadialDifferential (radialTruncationWeight ε R a (‖z‖ ^ 2))
      (radialTruncationSlope ε R a (‖z‖ ^ 2)) z‖ ≤
        (1 + 2 * a) * radialTruncationWeight ε R a (‖z‖ ^ 2) := by
  have hb := (radialTruncationBase_pos_le hε hR (sq_nonneg ‖z‖)).1
  have hd := radialTruncationSlope_mul_le hε hR ha (sq_nonneg ‖z‖)
  apply norm_complexRadialDifferential_le_weight _ _ (2 * a) z
    (Real.rpow_nonneg hb.le _) hd.1
  change 2 * radialTruncationSlope ε R a (‖z‖ ^ 2) * ‖z‖ ^ 2 ≤
    (2 * a) * radialTruncationWeight ε R a (‖z‖ ^ 2)
  nlinarith only [hd.2]

end EinsteinFull
