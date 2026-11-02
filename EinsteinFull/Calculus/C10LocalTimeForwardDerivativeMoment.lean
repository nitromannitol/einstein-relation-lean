import EinsteinFull.Calculus.C4LocalTimeDerivativeMoment
import EinsteinFull.Calculus.C10LocalTimeEnergyMoment

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull

/-- Subtract the actual scalar source from a corrected forward derivative.
The source contribution to the normalized energy is retained explicitly. -/
private theorem forward_derivative_source_subtraction
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0) (ht : 0 < (t : ℝ))
    (v : Lp ℂ 2 (reducedLaw Q))
    (hv : HasDerivAt (fun r : ℝ =>
      centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
        Lp.const 2 (reducedLaw Q)
          (∫ s in ((t : ℝ) / 4)..r, hP.centeringSource f s)) v (t : ℝ)) :
    let c := hP.centeringSource f (t : ℝ)
    let v₀ := v - Lp.const 2 (reducedLaw Q) c
    HasDerivAt (fun r : ℝ => centeredComplexLp Q (P r.toNNReal f)) v₀ (t : ℝ) ∧
      ∀ (ρ : ℝ) (hρ : 0 < ρ) (z : Vec d), ∀ᵐ ω ∂reducedLaw Q,
        localSpatialEnergy Q t ρ hρ z 0 v₀ ω ^ 2 ≤
          2 * (t : ℝ) * (⨍ x in {x | euclideanNorm (x - z) < ρ},
            ‖v (translate x ω)‖ ^ 2) + 2 * (t : ℝ) * ‖c‖ ^ 2 := by
  let := reducedLaw_probability Q
  intro c v₀
  have hc := ((Lp.constL 2 (reducedLaw Q) ℂ).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    (t : ℝ) (hasDerivAt_centered_source_primitive hP f ht ht)
  change HasDerivAt (fun r : ℝ => Lp.const 2 (reducedLaw Q)
    (∫ s in ((t : ℝ) / 4)..r, hP.centeringSource f s))
    (Lp.const 2 (reducedLaw Q) c) (t : ℝ) at hc
  have hd := hv.sub hc
  refine ⟨?_, ?_⟩
  · convert hd using 1
    funext r
    simp only [Pi.sub_apply, add_sub_cancel_right, hP.centered_apply]
  intro ρ hρ z
  let S := {x : Vec d | euclideanNorm (x - z) < ρ}
  have hvol := localSpatialEnergy_window_volume z ρ hρ
  have hSfin : volume S ≠ ∞ := (ENNReal.toReal_pos_iff.mp hvol).2.ne
  have hSzero : volume S ≠ 0 := (ENNReal.toReal_pos_iff.mp hvol).1.ne'
  let : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr hSfin
  have he : (fun ω => ‖v₀ ω‖ ^ 2) =ᵐ[reducedLaw Q]
      (fun ω => ‖v ω - c‖ ^ 2) := by
    filter_upwards [Lp.coeFn_sub v (Lp.const 2 (reducedLaw Q) c),
      Lp.coeFn_const 2 (reducedLaw Q) c] with ω hs hc
    simp only [v₀, hs, Pi.sub_apply, hc, Function.const_apply]
  have hephys := ae_ae_stationary_orbit_eq (reducedLaw_stationary Q)
    ((Lp.stronglyMeasurable v₀).measurable.norm.pow_const 2)
    (((Lp.stronglyMeasurable v).measurable.sub measurable_const).norm.pow_const 2) he
  have hz : (fun ω => ‖(0 : Lp ℂ 2 (reducedLaw Q)) ω‖) =ᵐ[reducedLaw Q]
      fun _ => (0 : ℝ) := by
    filter_upwards [Lp.coeFn_zero ℂ 2 (reducedLaw Q)] with ω hω
    simp only [hω, Pi.zero_apply, norm_zero]
  have hzphys := ae_ae_stationary_orbit_eq (reducedLaw_stationary Q)
    (Lp.stronglyMeasurable (0 : Lp ℂ 2 (reducedLaw Q))).measurable.norm
    measurable_const hz
  have hi := ae_integrableOn_stationary_orbit (reducedLaw_stationary Q)
    ((Lp.stronglyMeasurable v).measurable.norm.pow_const 2)
    ((Lp.memLp v).integrable_norm_pow (by norm_num)) hSfin
  have hi₀ := ae_integrableOn_stationary_orbit (reducedLaw_stationary Q)
    ((Lp.stronglyMeasurable v₀).measurable.norm.pow_const 2)
    ((Lp.memLp v₀).integrable_norm_pow (by norm_num)) hSfin
  filter_upwards [hephys, hzphys, hi, hi₀] with ω he hz hi hi₀
  have hpoint : ∀ᵐ x ∂volume.restrict S,
      ‖v₀ (translate x ω)‖ ^ 2 ≤ 2 * ‖v (translate x ω)‖ ^ 2 + 2 * ‖c‖ ^ 2 := by
    filter_upwards [ae_restrict_of_ae he] with x hx
    rw [hx]
    change ‖v (translate x ω) - c‖ ^ 2 ≤ _
    have hn := norm_sub_le (v (translate x ω)) c
    have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ ‖v (translate x ω)‖ + ‖c‖)).2 hn
    nlinarith only [hsq, sq_nonneg (‖v (translate x ω)‖ - ‖c‖)]
  have havg : (⨍ x in S, ‖v₀ (translate x ω)‖ ^ 2) ≤
      2 * (⨍ x in S, ‖v (translate x ω)‖ ^ 2) + 2 * ‖c‖ ^ 2 := by
    calc
      _ ≤ ⨍ x in S, 2 * ‖v (translate x ω)‖ ^ 2 + 2 * ‖c‖ ^ 2 := by
        simp only [average_eq, smul_eq_mul]
        exact mul_le_mul_of_nonneg_left
          (integral_mono_ae hi₀ ((hi.const_mul 2).add (integrable_const _)) hpoint)
          (by positivity)
      _ = _ := by
        simpa only [Pi.add_apply, average_const_mul, setAverage_const hSzero hSfin] using
          (average_add (hi.const_mul 2) (integrable_const (2 * ‖c‖ ^ 2)))
  have henergy : localSpatialEnergy Q t ρ hρ z 0 v₀ ω ^ 2 =
      (t : ℝ) * (⨍ x in S, ‖v₀ (translate x ω)‖ ^ 2) := by
    rw [localSpatialEnergy_sq]
    have heq : (fun x : Vec d =>
        (∑ j : Fin d, ‖(0 : Fin d → Lp ℂ 2 (reducedLaw Q)) j (translate x ω)‖ ^ 2) +
          (t : ℝ) * ‖v₀ (translate x ω)‖ ^ 2) =ᵐ[volume.restrict S]
        fun x => (t : ℝ) * ‖v₀ (translate x ω)‖ ^ 2 := by
      filter_upwards [ae_restrict_of_ae hz] with x hx
      simp only [Pi.zero_apply, hx, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, Finset.sum_const_zero, zero_add]
    rw [average_congr heq, average_const_mul]
  rw [henergy]
  calc
    _ ≤ (t : ℝ) * (2 * (⨍ x in S, ‖v (translate x ω)‖ ^ 2) + 2 * ‖c‖ ^ 2) :=
      mul_le_mul_of_nonneg_left havg t.property
    _ = _ := by ring

/-- Every permitted endpoint is the centered forward orbit of its own initial
value, including the clock at zero force. -/
private theorem forward_endpoint_restarts
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (ζ : ℂ) (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (ν : EndpointIndex d) (hν : ν ≠ .inr true) (t : ℝ≥0) :
    indexedEndpoint hd Q ν ζ P Pdag β a μ t =
      centeredComplexLp Q (P t (indexedEndpoint hd Q ν ζ P Pdag β a μ 0)) := by
  cases ν with
  | inl k =>
    simp only [indexedEndpoint, velocityEndpoint, hP.1, ContinuousLinearMap.id_apply,
      hP.centered_apply]
  | inr b =>
    cases b with
    | true => exact False.elim (hν rfl)
    | false =>
      simp only [indexedEndpoint, clockEndpoint, hP.1, ContinuousLinearMap.id_apply]
      rw [map_smul, ← centeredComplexLpCLM_apply Q (ζ • P t (centeredComplexLp Q μ)),
        map_smul, centeredComplexLpCLM_apply, hP.centered_apply]

/-- Removing the actual source preserves the forward derivative moment, with
both contributions explicit before the structural constants are absorbed. -/
private theorem forward_derivative_moment_with_source
    (h0 : node_l_u3A_forced_u2D_local_u23_centered_u2D_sourceStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C₀ Cs : ℝ, 0 < C₀ ∧ 0 < Cs ∧
    ∀ p : ℝ, 2 ≤ p → ∃ Cp : ℝ, 0 < Cp ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q) (ζ : ℂ)
      (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
      (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
      (f : Lp ℂ 2 (reducedLaw Q)),
      MemLp f (ENNReal.ofReal p) (reducedLaw Q) →
    ∀ (t : ℝ≥0) (ht : 0 < (t : ℝ)),
    let u := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f))
    MemLp (u ((t : ℝ) / 8)) (ENNReal.ofReal p) (reducedLaw Q) ∧
    ∃ v : Lp ℂ 2 (reducedLaw Q),
      HasDerivAt (fun r : ℝ => centeredComplexLp Q (P r.toNNReal f)) v (t : ℝ) ∧
      ∀ (ρ : ℝ) (z : Vec d) (hρ : Real.sqrt (t : ℝ) ≤ ρ),
        MemLp (localSpatialEnergy Q t ρ ((Real.sqrt_pos.mpr ht).trans_le hρ)
          z 0 v) (ENNReal.ofReal p) (reducedLaw Q) ∧
        eLpNorm (localSpatialEnergy Q t ρ ((Real.sqrt_pos.mpr ht).trans_le hρ)
          z 0 v) (ENNReal.ofReal p) (reducedLaw Q) ≤
          ENNReal.ofReal
            (2 * Real.sqrt (C₀ * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ 6 / (t : ℝ)) *
                (Cp * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) *
                  Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ))) +
              2 * Cs * ‖ζ‖ * Real.exp (Cs * ‖ζ‖ ^ 2 * (t : ℝ))) *
            eLpNorm (u ((t : ℝ) / 8)) (ENNReal.ofReal p) (reducedLaw Q) := by
  obtain ⟨C₀, hC₀, hmoment⟩ :=
    local_time_corrected_derivative_moment_of_source_dependency h0 d hd D
  obtain ⟨Cs, hCs, hsource⟩ :=
    local_time_corrected_cylinder_of_source_dependency h0 d hd D
  refine ⟨C₀, Cs, hC₀, hCs, ?_⟩
  intro p hp
  obtain ⟨Cp, hCp, hmoment⟩ := hmoment p hp
  obtain ⟨_, _, hsource⟩ := hsource p hp
  refine ⟨Cp, hCp, ?_⟩
  intro Q hQ ζ P hP f hf t ht u
  let := reducedLaw_probability Q
  obtain ⟨hu8, v, hv, hvm⟩ := hmoment Q hQ ζ P hP f hf t ht
  obtain ⟨_, _, hcs, _⟩ := hsource Q hQ ζ P hP f hf (t : ℝ) ht
  obtain ⟨hv₀, hsq⟩ := forward_derivative_source_subtraction hP f t ht v hv
  refine ⟨hu8, v - Lp.const 2 (reducedLaw Q) (hP.centeringSource f (t : ℝ)), hv₀, ?_⟩
  have hp0 : 0 < p := by linarith
  have hpe : 1 ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using
      ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith)
  have hp2 : (2 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hp
  have hn8 : ‖u ((t : ℝ) / 8)‖ ≤
      (eLpNorm (u ((t : ℝ) / 8)) (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
    rw [Lp.norm_def]
    exact ENNReal.toReal_mono hu8.eLpNorm_ne_top
      (eLpNorm_le_eLpNorm_of_exponent_le hp2)
  have hcs' := (hcs (t : ℝ) ⟨by linarith, le_rfl⟩).trans
    (mul_le_mul_of_nonneg_left hn8 (by positivity))
  intro ρ z hρ
  let hρpos := (Real.sqrt_pos.mpr ht).trans_le hρ
  let E := localSpatialEnergy Q t ρ hρpos z 0 v
  let c := hP.centeringSource f (t : ℝ)
  let b := 2 * Real.sqrt (t : ℝ) * ‖c‖
  let H := fun ω => 2 * E ω + b
  obtain ⟨hE, hEm⟩ := hvm ρ z hρ
  have hb : 0 ≤ b := by positivity
  have hH : MemLp H (ENNReal.ofReal p) (reducedLaw Q) :=
    (hE.const_mul 2).add (memLp_const b)
  have hdom : ∀ᵐ ω ∂reducedLaw Q,
      ‖localSpatialEnergy Q t ρ hρpos z 0
        (v - Lp.const 2 (reducedLaw Q) c) ω‖ ≤ H ω := by
    filter_upwards [hsq ρ hρpos z,
      local_time_zero_gradient_energy_sq Q t ρ hρpos z v] with ω hs he
    have hEpos : 0 ≤ E ω := Real.sqrt_nonneg _
    have hvpos : 0 ≤ localSpatialEnergy Q t ρ hρpos z 0
        (v - Lp.const 2 (reducedLaw Q) c) ω := Real.sqrt_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hvpos]
    apply (sq_le_sq₀ hvpos (show 0 ≤ H ω by dsimp [H]; positivity)).mp
    have hb2 : b ^ 2 = 4 * (t : ℝ) * ‖c‖ ^ 2 := by
      dsimp [b]; rw [mul_pow, mul_pow, Real.sq_sqrt ht.le]; ring
    change E ω ^ 2 = _ at he
    dsimp [H]
    nlinarith [mul_nonneg hEpos hb, sq_nonneg (E ω)]
  have hm := localSpatialEnergy_aestronglyMeasurable Q t ρ hρpos z 0
    (v - Lp.const 2 (reducedLaw Q) c)
  refine ⟨hH.mono' hm hdom, ?_⟩
  have hbn : eLpNorm (fun _ : FieldPair d => b) (ENNReal.ofReal p) (reducedLaw Q) ≤
      ENNReal.ofReal (2 * Cs * ‖ζ‖ * Real.exp (Cs * ‖ζ‖ ^ 2 * (t : ℝ))) *
        eLpNorm (u ((t : ℝ) / 8)) (ENNReal.ofReal p) (reducedLaw Q) := by
    rw [eLpNorm_const' b (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top,
      measure_univ, ENNReal.one_rpow, mul_one, Real.enorm_eq_ofReal_abs,
      abs_of_nonneg hb]
    have hbnd : b ≤ 2 * Cs * ‖ζ‖ * Real.exp (Cs * ‖ζ‖ ^ 2 * (t : ℝ)) *
        (eLpNorm (u ((t : ℝ) / 8)) (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
      calc
        b ≤ 2 * Real.sqrt (t : ℝ) *
            (Cs * ‖ζ‖ / Real.sqrt (t : ℝ) * Real.exp (Cs * ‖ζ‖ ^ 2 * (t : ℝ)) *
              (eLpNorm (u ((t : ℝ) / 8)) (ENNReal.ofReal p) (reducedLaw Q)).toReal) :=
          mul_le_mul_of_nonneg_left hcs' (by positivity)
        _ = _ := by field_simp
    calc
      _ ≤ ENNReal.ofReal _ := ENNReal.ofReal_le_ofReal hbnd
      _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hu8.eLpNorm_ne_top]
  have hscalar : eLpNorm (fun ω => 2 * E ω) (ENNReal.ofReal p) (reducedLaw Q) =
      ENNReal.ofReal 2 * eLpNorm E (ENNReal.ofReal p) (reducedLaw Q) := by
    change eLpNorm ((2 : ℝ) • E) _ _ = _
    simpa only [Real.enorm_eq_ofReal_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] using (eLpNorm_const_smul (c := (2 : ℝ)) (f := E)
      (p := ENNReal.ofReal p) (μ := reducedLaw Q))
  calc
    _ ≤ eLpNorm H (ENNReal.ofReal p) (reducedLaw Q) :=
      eLpNorm_mono_ae_real hm hdom
    _ ≤ eLpNorm (fun ω => 2 * E ω) (ENNReal.ofReal p) (reducedLaw Q) +
        eLpNorm (fun _ : FieldPair d => b) (ENNReal.ofReal p) (reducedLaw Q) :=
      eLpNorm_add_le hpe
    _ ≤ ENNReal.ofReal 2 *
        (ENNReal.ofReal (Real.sqrt (C₀ * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ 6 / (t : ℝ))) *
          (ENNReal.ofReal (Cp * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) *
            Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)))) *
            eLpNorm (u ((t : ℝ) / 8)) (ENNReal.ofReal p) (reducedLaw Q)) +
        ENNReal.ofReal (2 * Cs * ‖ζ‖ * Real.exp (Cs * ‖ζ‖ ^ 2 * (t : ℝ))) *
          eLpNorm (u ((t : ℝ) / 8)) (ENNReal.ofReal p) (reducedLaw Q) := by
      rw [hscalar]
      apply add_le_add _ hbn
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [mul_assoc] using hEm
    _ = _ := by
      rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity), ← add_mul,
        ← ENNReal.ofReal_add (by positivity) (by positivity)]

theorem local_time_forward_derivative_moment_of_deps
  (h0 : EinsteinFull.Blueprint.node_l_u3A_forced_u2D_local_u23_centered_u2D_sourceStmt)
  (h1 : EinsteinFull.Blueprint.node_e_u3A_lp_u2D_growthStmt) :
∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∀ p : ℝ, 2 ≤ p → ∃ C Cp : ℝ, 1 ≤ C ∧ 0 < Cp ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d, ν ≠ .inr true →
    ∃ G : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
    ∃ V : ℝ≥0 → Lp ℂ 2 (reducedLaw Q),
    (∀ t : ℝ≥0, 0 < (t : ℝ) →
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (indexedEndpoint hd Q ν ζ P Pdag β a μ t) (G t) ∧
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (uncenteredEndpoint hd Q ν ζ P Pdag β a μ t) (G t) ∧
      HasDerivAt (fun r : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ r.toNNReal)
        (V t) (t : ℝ)) ∧
    (∀ (t : ℝ≥0) (ht : 0 < (t : ℝ)),
      let U := indexedEndpoint hd Q ν ζ P Pdag β a μ t
      let U₈ := indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8)
      MemLp (U₈ : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
      (∀ (ρ : ℝ) (x : Vec d) (hρ : Real.sqrt (t : ℝ) ≤ ρ),
        MemLp (localSpatialEnergy Q t ρ (lt_of_lt_of_le (Real.sqrt_pos.mpr ht) hρ) x (0) (V t)) (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm (localSpatialEnergy Q t ρ (lt_of_lt_of_le (Real.sqrt_pos.mpr ht) hρ) x (0) (V t))
          (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        C * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C * (t : ℝ) ^ (-(1 / 2 : ℝ)) *
          Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
          (eLpNorm (U₈ : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal)) := by
  intro d hd D p hp
  obtain ⟨C₀, Cs, hC₀, hCs, hmoment⟩ := forward_derivative_moment_with_source h0 d hd D
  obtain ⟨Cp, hCp, hmoment⟩ := hmoment p hp
  let C := max 4 (2 * Real.sqrt C₀ * Cp + 2 * Cs)
  let B := max Cp Cs
  have hC4 : 4 ≤ C := le_max_left _ _
  have hCA : 2 * Real.sqrt C₀ * Cp + 2 * Cs ≤ C := le_max_right _ _
  have hB : 0 < B := hCp.trans_le (le_max_left _ _)
  refine ⟨C, B, by linarith, hB, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hν
  obtain ⟨G, V, hGV⟩ := local_time_endpoint_witnesses hd Q hQ β a μ hβ ha hμ
    ζ P Pdag hP hPdag ν
  refine ⟨G, V, hGV, ?_⟩
  intro t ht U U₈
  let f := indexedEndpoint hd Q ν ζ P Pdag β a μ 0
  have hf := local_time_endpoint_memLp h1 hd p hp Q hQ β a μ hβ ha hμ
    ζ P Pdag hP hPdag ν 0
  obtain ⟨hu8, v, hv, hvm⟩ := hmoment Q hQ ζ P hP f hf t ht
  have horbit (r : ℝ) :
      centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) =
        indexedEndpoint hd Q ν ζ P Pdag β a μ r.toNNReal := by
    rw [hP.centered_apply]
    exact (forward_endpoint_restarts hd Q β a μ ζ P Pdag hP ν hν r.toNNReal).symm
  have ht8 : ((t : ℝ) / 8).toNNReal = t / 8 := by
    apply NNReal.coe_injective
    rw [Real.coe_toNNReal _ (by positivity)]
    simp
  have hu8eq : centeredComplexLp Q (P ((t : ℝ) / 8).toNNReal
      (centeredComplexLp Q f)) = U₈ := by rw [horbit, ht8]
  dsimp only at hu8
  rw [hu8eq] at hu8
  have hv' : HasDerivAt
      (fun r : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ r.toNNReal) v (t : ℝ) := by
    convert hv using 1
    funext r
    exact forward_endpoint_restarts hd Q β a μ ζ P Pdag hP ν hν r.toNNReal
  have hvV : v = V t := hv'.unique (hGV t ht).2.2
  refine ⟨hu8, ?_⟩
  intro ρ x hρ
  obtain ⟨hm, hnorm⟩ := hvm ρ x hρ
  rw [hvV] at hm hnorm
  dsimp only at hnorm
  rw [hu8eq] at hnorm
  refine ⟨hm, ?_⟩
  let s := Real.sqrt (t : ℝ)
  let k := 1 + ‖ζ‖ * s
  have hs : 0 < s := Real.sqrt_pos.mpr ht
  have hk : 1 ≤ k := le_add_of_nonneg_right (mul_nonneg (norm_nonneg ζ) hs.le)
  have hk0 : 0 ≤ k := by linarith
  have hroot : Real.sqrt (C₀ * k ^ 6 / (t : ℝ)) = Real.sqrt C₀ * k ^ 3 / s := by
    rw [Real.sqrt_div (by positivity), Real.sqrt_mul hC₀.le,
      show k ^ 6 = (k ^ 3) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have heCp : Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) ≤
      Real.exp (B * ‖ζ‖ ^ 2 * (t : ℝ)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left Cp Cs) (sq_nonneg _)) ht.le
  have heCs : Real.exp (Cs * ‖ζ‖ ^ 2 * (t : ℝ)) ≤
      Real.exp (B * ‖ζ‖ ^ 2 * (t : ℝ)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right Cp Cs) (sq_nonneg _)) ht.le
  have hk4 : k ≤ k ^ 4 := by
    have hk2 : k ≤ k ^ 2 := by nlinarith [mul_nonneg hk0 (sub_nonneg.mpr hk)]
    nlinarith [sq_nonneg (k ^ 2 - 1)]
  have hz : ‖ζ‖ ≤ k ^ 4 / s := by
    apply (le_div_iff₀ hs).mpr
    exact (show ‖ζ‖ * s ≤ k by dsimp [k]; linarith).trans hk4
  have hcoef :
      2 * Real.sqrt (C₀ * k ^ 6 / (t : ℝ)) *
          (Cp * k * Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ))) +
        2 * Cs * ‖ζ‖ * Real.exp (Cs * ‖ζ‖ ^ 2 * (t : ℝ)) ≤
      C * k ^ C * (t : ℝ) ^ (-(1 / 2 : ℝ)) *
        Real.exp (B * ‖ζ‖ ^ 2 * (t : ℝ)) := by
    have hfirst : 2 * Real.sqrt (C₀ * k ^ 6 / (t : ℝ)) *
        (Cp * k * Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ))) ≤
        (2 * Real.sqrt C₀ * Cp * k ^ 4 / s) *
          Real.exp (B * ‖ζ‖ ^ 2 * (t : ℝ)) := by
      rw [hroot]
      calc
        _ = (2 * Real.sqrt C₀ * Cp * k ^ 4 / s) *
            Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left heCp (by positivity)
    have hsecond : 2 * Cs * ‖ζ‖ * Real.exp (Cs * ‖ζ‖ ^ 2 * (t : ℝ)) ≤
        (2 * Cs * k ^ 4 / s) * Real.exp (B * ‖ζ‖ ^ 2 * (t : ℝ)) := by
      calc
        _ ≤ (2 * Cs * (k ^ 4 / s)) *
            Real.exp (B * ‖ζ‖ ^ 2 * (t : ℝ)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hz (by positivity)) heCs
            (by positivity) (by positivity)
        _ = _ := by ring
    have hpows : k ^ 4 ≤ k ^ C := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hk hC4
    have hinv : (t : ℝ) ^ (-(1 / 2 : ℝ)) = s⁻¹ := by
      rw [Real.rpow_neg ht.le, ← Real.sqrt_eq_rpow]
    calc
      _ ≤ (2 * Real.sqrt C₀ * Cp * k ^ 4 / s) * Real.exp (B * ‖ζ‖ ^ 2 * (t : ℝ)) +
          (2 * Cs * k ^ 4 / s) * Real.exp (B * ‖ζ‖ ^ 2 * (t : ℝ)) :=
        add_le_add hfirst hsecond
      _ = (2 * Real.sqrt C₀ * Cp + 2 * Cs) * k ^ 4 / s *
          Real.exp (B * ‖ζ‖ ^ 2 * (t : ℝ)) := by ring
      _ ≤ C * k ^ C / s * Real.exp (B * ‖ζ‖ ^ 2 * (t : ℝ)) := by
        gcongr
      _ = _ := by rw [hinv]; ring
  have hreal := ENNReal.toReal_mono
    (show ENNReal.ofReal _ * eLpNorm (U₈ : FieldPair d → ℂ)
      (ENNReal.ofReal p) (reducedLaw Q) ≠ ∞ from
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hu8.eLpNorm_ne_top) hnorm
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at hreal
  exact hreal.trans (mul_le_mul_of_nonneg_right hcoef ENNReal.toReal_nonneg)

#print axioms local_time_forward_derivative_moment_of_deps
#print axioms forward_derivative_source_subtraction
#print axioms forward_endpoint_restarts
#print axioms forward_derivative_moment_with_source

end EinsteinFull.Blueprint

#lint
