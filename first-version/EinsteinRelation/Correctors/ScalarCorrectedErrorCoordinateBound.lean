import EinsteinRelation.Correctors.BoundedCoefficientMoments
import EinsteinRelation.Correctors.ScalarDecompositionSums

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinRelation.Correctors

/-- A coordinate of the corrected flux error has the scale `a/r`
(`paper/main.tex:1056–1075`). -/
theorem scalarCorrected_error_scalar_coordinate
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d : ℕ} {p r a A B L : ℝ} (hp : 1 ≤ p) (hr : 1 ≤ r) (ha : 1 ≤ a)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hL : 0 ≤ L)
    (c S : Fin d → Fin d → Ω → ℝ) (phi D : Fin d → Ω → ℝ)
    (H : Fin d → Fin d → Ω → ℝ) (F : Fin d → Ω → ℝ)
    (hc : ∀ j k, Measurable (c j k)) (hS : ∀ j k, Measurable (S j k))
    (hphi : ∀ j, Measurable (phi j)) (hD : ∀ j, Measurable (D j))
    (hH : ∀ j k, Measurable (H j k)) (hF : ∀ j, Measurable (F j))
    (hcb : ∀ᵐ ω ∂μ, ∀ j k, |c j k ω| ≤ L)
    (hSb : ∀ j k, eLpNorm (S j k) (ENNReal.ofReal (4 * p)) μ ≤ ENNReal.ofReal (A * a))
    (hphib : ∀ j, eLpNorm (phi j) (ENNReal.ofReal (4 * p)) μ ≤ ENNReal.ofReal (A * a))
    (hDb : ∀ j, eLpNorm (D j) (ENNReal.ofReal (4 * p)) μ ≤ ENNReal.ofReal B)
    (hHb : ∀ j k, eLpNorm (H j k) (ENNReal.ofReal (4 * p)) μ ≤ ENNReal.ofReal (B / r))
    (hFb : ∀ j, eLpNorm (F j) (ENNReal.ofReal (4 * p)) μ ≤ ENNReal.ofReal (A / r)) :
    eLpNorm (fun ω => ∑ j, ((phi j ω * ∑ k, c j k ω * H j k ω) -
      (∑ k, S j k ω * H j k ω) + D j ω * F j ω)) (ENNReal.ofReal (2 * p)) μ ≤
      ENNReal.ofReal ((((d : ℝ)^2 * (L + 1) + d) * A * B) * (a / r)) := by
  have ha_pos : 0 ≤ a := by linarith
  have hr_pos : 0 ≤ r := by linarith
  have h_one_le_2p : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (2 * p) :=
    ENNReal.one_le_ofReal.mpr (by linarith)
  have h_one_le_4p : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (4 * p) :=
    ENNReal.one_le_ofReal.mpr (by linarith)
  -- AEStronglyMeasurable helpers
  have h_meas_c (j k : Fin d) : AEStronglyMeasurable (c j k) μ :=
    (hc j k).aestronglyMeasurable
  have h_meas_S (j k : Fin d) : AEStronglyMeasurable (S j k) μ :=
    (hS j k).aestronglyMeasurable
  have h_meas_phi (j : Fin d) : AEStronglyMeasurable (phi j) μ :=
    (hphi j).aestronglyMeasurable
  have h_meas_D (j : Fin d) : AEStronglyMeasurable (D j) μ :=
    (hD j).aestronglyMeasurable
  have h_meas_H (j k : Fin d) : AEStronglyMeasurable (H j k) μ :=
    (hH j k).aestronglyMeasurable
  have h_meas_F (j : Fin d) : AEStronglyMeasurable (F j) μ :=
    (hF j).aestronglyMeasurable
  -- inner sum functions
  set inner_cH : Fin d → Ω → ℝ := fun j ω => ∑ k : Fin d, c j k ω * H j k ω with h_inner_cH_def
  set inner_SH : Fin d → Ω → ℝ := fun j ω => ∑ k : Fin d, S j k ω * H j k ω with h_inner_SH_def
  have h_meas_inner_cH (j : Fin d) : AEStronglyMeasurable (inner_cH j) μ := by
    rw [h_inner_cH_def]
    have h : AEStronglyMeasurable (∑ k ∈ Finset.univ, (c j k * H j k)) μ :=
      Finset.aestronglyMeasurable_sum (Finset.univ : Finset (Fin d)) (fun k _ =>
        (h_meas_c j k).mul (h_meas_H j k))
    have heq : (∑ k ∈ Finset.univ, (c j k * H j k)) = (fun ω => ∑ k ∈ Finset.univ, c j k ω * H j k ω) := by
      ext ω; simp
    simpa [heq] using h
  have h_meas_inner_SH (j : Fin d) : AEStronglyMeasurable (inner_SH j) μ := by
    rw [h_inner_SH_def]
    have h : AEStronglyMeasurable (∑ k ∈ Finset.univ, (S j k * H j k)) μ :=
      Finset.aestronglyMeasurable_sum (Finset.univ : Finset (Fin d)) (fun k _ =>
        (h_meas_S j k).mul (h_meas_H j k))
    have heq : (∑ k ∈ Finset.univ, (S j k * H j k)) = (fun ω => ∑ k ∈ Finset.univ, S j k ω * H j k ω) := by
      ext ω; simp
    simpa [heq] using h
  -- bound for inner_cH j at L^{4p}
  have h_inner_cH_bound_4p (j : Fin d) :
      eLpNorm (inner_cH j) (ENNReal.ofReal (4 * p)) μ ≤
        ENNReal.ofReal ((d : ℝ) * L * (B / r)) := by
    rw [h_inner_cH_def]
    have hsum : eLpNorm (fun ω => ∑ k : Fin d, c j k ω * H j k ω) (ENNReal.ofReal (4 * p)) μ ≤
        ∑ k : Fin d, eLpNorm (fun ω => c j k ω * H j k ω) (ENNReal.ofReal (4 * p)) μ := by
      simpa using eLpNorm_finset_sum_le (Finset.univ : Finset (Fin d))
        (fun k ω => c j k ω * H j k ω)
        (fun k _ => (h_meas_c j k).mul (h_meas_H j k))
        h_one_le_4p
    have hterm (k : Fin d) : eLpNorm (fun ω => c j k ω * H j k ω) (ENNReal.ofReal (4 * p)) μ ≤
        ENNReal.ofReal (L * (B / r)) := by
      have h := eLpNorm_bounded_mul_le hL (hcb.mono fun ω hω => hω j k) (hHb j k)
      simpa [mul_comm] using h
    have hsum2 : (∑ k : Fin d, eLpNorm (fun ω => c j k ω * H j k ω) (ENNReal.ofReal (4 * p)) μ) ≤
        ∑ k : Fin d, ENNReal.ofReal (L * (B / r)) :=
      Finset.sum_le_sum fun k _ => hterm k
    have hsum3 : (∑ k : Fin d, ENNReal.ofReal (L * (B / r))) =
        (d : ℝ≥0∞) * ENNReal.ofReal (L * (B / r)) := by simp
    have hsum4 : (d : ℝ≥0∞) * ENNReal.ofReal (L * (B / r)) =
        ENNReal.ofReal ((d : ℝ) * (L * (B / r))) := by
      calc
        (d : ℝ≥0∞) * ENNReal.ofReal (L * (B / r))
            = ENNReal.ofReal (d : ℝ) * ENNReal.ofReal (L * (B / r)) := by simp
        _ = ENNReal.ofReal ((d : ℝ) * (L * (B / r))) := by
          rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (d : ℝ))]
    have hsum5 : ENNReal.ofReal ((d : ℝ) * (L * (B / r))) =
        ENNReal.ofReal ((d : ℝ) * L * (B / r)) := by ring
    calc
      eLpNorm (fun ω => ∑ k : Fin d, c j k ω * H j k ω) (ENNReal.ofReal (4 * p)) μ
          ≤ ∑ k : Fin d, eLpNorm (fun ω => c j k ω * H j k ω) (ENNReal.ofReal (4 * p)) μ := hsum
      _ ≤ ∑ k : Fin d, ENNReal.ofReal (L * (B / r)) := hsum2
      _ = (d : ℝ≥0∞) * ENNReal.ofReal (L * (B / r)) := hsum3
      _ = ENNReal.ofReal ((d : ℝ) * (L * (B / r))) := hsum4
      _ = ENNReal.ofReal ((d : ℝ) * L * (B / r)) := hsum5
  -- bound for phi j * inner_cH j at L^{2p}
  have h_phi_inner_bound (j : Fin d) :
      eLpNorm (fun ω => phi j ω * inner_cH j ω) (ENNReal.ofReal (2 * p)) μ ≤
        ENNReal.ofReal ((d : ℝ) * L * A * B * (a / r)) := by
    have h_mul := eLpNorm_mul_le_holder_four hp (h_meas_phi j) (h_meas_inner_cH j)
    have h_bound : eLpNorm (phi j) (ENNReal.ofReal (4 * p)) μ *
        eLpNorm (inner_cH j) (ENNReal.ofReal (4 * p)) μ ≤
        ENNReal.ofReal (A * a) * ENNReal.ofReal ((d : ℝ) * L * (B / r)) :=
      mul_le_mul' (hphib j) (h_inner_cH_bound_4p j)
    have h_prod : ENNReal.ofReal (A * a) * ENNReal.ofReal ((d : ℝ) * L * (B / r)) =
        ENNReal.ofReal ((d : ℝ) * L * A * B * (a / r)) := by
      calc
        ENNReal.ofReal (A * a) * ENNReal.ofReal ((d : ℝ) * L * (B / r))
            = ENNReal.ofReal (A * a * ((d : ℝ) * L * (B / r))) := by
          rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ A * a)]
        _ = ENNReal.ofReal ((d : ℝ) * L * A * B * (a / r)) := by ring
    calc
      eLpNorm (fun ω => phi j ω * inner_cH j ω) (ENNReal.ofReal (2 * p)) μ
          ≤ eLpNorm (phi j) (ENNReal.ofReal (4 * p)) μ *
            eLpNorm (inner_cH j) (ENNReal.ofReal (4 * p)) μ := h_mul
      _ ≤ ENNReal.ofReal (A * a) * ENNReal.ofReal ((d : ℝ) * L * (B / r)) := h_bound
      _ = ENNReal.ofReal ((d : ℝ) * L * A * B * (a / r)) := h_prod
  -- bound for inner_SH j at L^{2p}
  have h_inner_SH_bound (j : Fin d) :
      eLpNorm (inner_SH j) (ENNReal.ofReal (2 * p)) μ ≤
        ENNReal.ofReal ((d : ℝ) * A * B * (a / r)) := by
    rw [h_inner_SH_def]
    have hsum : eLpNorm (fun ω => ∑ k : Fin d, S j k ω * H j k ω) (ENNReal.ofReal (2 * p)) μ ≤
        ∑ k : Fin d, eLpNorm (fun ω => S j k ω * H j k ω) (ENNReal.ofReal (2 * p)) μ := by
      simpa using eLpNorm_finset_sum_le (Finset.univ : Finset (Fin d))
        (fun k ω => S j k ω * H j k ω)
        (fun k _ => (h_meas_S j k).mul (h_meas_H j k))
        h_one_le_2p
    have hterm (k : Fin d) : eLpNorm (fun ω => S j k ω * H j k ω) (ENNReal.ofReal (2 * p)) μ ≤
        eLpNorm (S j k) (ENNReal.ofReal (4 * p)) μ * eLpNorm (H j k) (ENNReal.ofReal (4 * p)) μ :=
      eLpNorm_mul_le_holder_four hp (h_meas_S j k) (h_meas_H j k)
    have hsum2 : (∑ k : Fin d, eLpNorm (fun ω => S j k ω * H j k ω) (ENNReal.ofReal (2 * p)) μ) ≤
        ∑ k : Fin d, (eLpNorm (S j k) (ENNReal.ofReal (4 * p)) μ *
          eLpNorm (H j k) (ENNReal.ofReal (4 * p)) μ) :=
      Finset.sum_le_sum fun k _ => hterm k
    have hsum3 : (∑ k : Fin d, (eLpNorm (S j k) (ENNReal.ofReal (4 * p)) μ *
        eLpNorm (H j k) (ENNReal.ofReal (4 * p)) μ)) ≤
        ∑ k : Fin d, (ENNReal.ofReal (A * a) * ENNReal.ofReal (B / r)) :=
      Finset.sum_le_sum fun k _ => mul_le_mul' (hSb j k) (hHb j k)
    have hsum4 : (∑ k : Fin d, (ENNReal.ofReal (A * a) * ENNReal.ofReal (B / r))) =
        (d : ℝ≥0∞) * (ENNReal.ofReal (A * a) * ENNReal.ofReal (B / r)) := by simp
    have hsum5 : (d : ℝ≥0∞) * (ENNReal.ofReal (A * a) * ENNReal.ofReal (B / r)) =
        ENNReal.ofReal ((d : ℝ) * A * B * (a / r)) := by
      calc
        (d : ℝ≥0∞) * (ENNReal.ofReal (A * a) * ENNReal.ofReal (B / r))
            = ENNReal.ofReal (A * a) * ENNReal.ofReal (B / r) * (d : ℝ≥0∞) := by ring
        _ = ENNReal.ofReal (A * a * (B / r)) * (d : ℝ≥0∞) := by
          rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ A * a)]
        _ = ENNReal.ofReal ((d : ℝ) * (A * a * (B / r))) := by
          calc
            ENNReal.ofReal (A * a * (B / r)) * (d : ℝ≥0∞)
                = ENNReal.ofReal (A * a * (B / r)) * ENNReal.ofReal (d : ℝ) := by simp
            _ = ENNReal.ofReal ((A * a * (B / r)) * (d : ℝ)) := by
              rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ A * a * (B / r))]
            _ = ENNReal.ofReal ((d : ℝ) * (A * a * (B / r))) := by ring
        _ = ENNReal.ofReal ((d : ℝ) * A * B * (a / r)) := by ring
    calc
      eLpNorm (fun ω => ∑ k : Fin d, S j k ω * H j k ω) (ENNReal.ofReal (2 * p)) μ
          ≤ ∑ k : Fin d, eLpNorm (fun ω => S j k ω * H j k ω) (ENNReal.ofReal (2 * p)) μ := hsum
      _ ≤ ∑ k : Fin d, (eLpNorm (S j k) (ENNReal.ofReal (4 * p)) μ *
          eLpNorm (H j k) (ENNReal.ofReal (4 * p)) μ) := hsum2
      _ ≤ ∑ k : Fin d, (ENNReal.ofReal (A * a) * ENNReal.ofReal (B / r)) := hsum3
      _ = (d : ℝ≥0∞) * (ENNReal.ofReal (A * a) * ENNReal.ofReal (B / r)) := hsum4
      _ = ENNReal.ofReal ((d : ℝ) * A * B * (a / r)) := hsum5
  -- bound for D j * F j at L^{2p}
  have h_DF_bound (j : Fin d) :
      eLpNorm (fun ω => D j ω * F j ω) (ENNReal.ofReal (2 * p)) μ ≤
        ENNReal.ofReal (A * B * (a / r)) := by
    have h_mul := eLpNorm_mul_le_holder_four hp (h_meas_D j) (h_meas_F j)
    have h_bound : eLpNorm (D j) (ENNReal.ofReal (4 * p)) μ *
        eLpNorm (F j) (ENNReal.ofReal (4 * p)) μ ≤
        ENNReal.ofReal B * ENNReal.ofReal (A / r) :=
      mul_le_mul' (hDb j) (hFb j)
    have h_prod : ENNReal.ofReal B * ENNReal.ofReal (A / r) ≤
        ENNReal.ofReal (A * B * (a / r)) := by
      calc
        ENNReal.ofReal B * ENNReal.ofReal (A / r) = ENNReal.ofReal (B * (A / r)) := by
          rw [← ENNReal.ofReal_mul hB]
        _ = ENNReal.ofReal (A * B / r) := by ring
        _ ≤ ENNReal.ofReal (A * B * (a / r)) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hpos : 0 ≤ A * B := mul_nonneg hA hB
          calc
            A * B / r = (A * B) * (1 / r) := by ring
            _ ≤ (A * B) * (a / r) := by
              gcongr
            _ = A * B * (a / r) := by ring
    calc
      eLpNorm (fun ω => D j ω * F j ω) (ENNReal.ofReal (2 * p)) μ
          ≤ eLpNorm (D j) (ENNReal.ofReal (4 * p)) μ *
            eLpNorm (F j) (ENNReal.ofReal (4 * p)) μ := h_mul
      _ ≤ ENNReal.ofReal B * ENNReal.ofReal (A / r) := h_bound
      _ ≤ ENNReal.ofReal (A * B * (a / r)) := h_prod
  -- bound for each j: the whole inner expression at L^{2p}
  have h_single_j_bound (j : Fin d) :
      eLpNorm (fun ω => (phi j ω * inner_cH j ω) - inner_SH j ω + D j ω * F j ω)
        (ENNReal.ofReal (2 * p)) μ ≤
        ENNReal.ofReal (((d : ℝ) * L + (d : ℝ) + 1) * A * B * (a / r)) := by
    have hA : AEStronglyMeasurable (fun ω => phi j ω * inner_cH j ω) μ :=
      (h_meas_phi j).mul (h_meas_inner_cH j)
    have hB : AEStronglyMeasurable (inner_SH j) μ := h_meas_inner_SH j
    have hC : AEStronglyMeasurable (fun ω => D j ω * F j ω) μ :=
      (h_meas_D j).mul (h_meas_F j)
    have h_AB : AEStronglyMeasurable (fun ω => (phi j ω * inner_cH j ω) - inner_SH j ω) μ :=
      hA.sub hB
    have h_add := eLpNorm_add_le h_AB hC h_one_le_2p
    have h_sub := eLpNorm_sub_le hA hB h_one_le_2p
    have h_total : eLpNorm (fun ω => (phi j ω * inner_cH j ω) - inner_SH j ω + D j ω * F j ω)
        (ENNReal.ofReal (2 * p)) μ ≤
        eLpNorm (fun ω => phi j ω * inner_cH j ω) (ENNReal.ofReal (2 * p)) μ +
        eLpNorm (inner_SH j) (ENNReal.ofReal (2 * p)) μ +
        eLpNorm (fun ω => D j ω * F j ω) (ENNReal.ofReal (2 * p)) μ := by
      calc
        eLpNorm (fun ω => (phi j ω * inner_cH j ω) - inner_SH j ω + D j ω * F j ω)
            (ENNReal.ofReal (2 * p)) μ
            ≤ eLpNorm (fun ω => (phi j ω * inner_cH j ω) - inner_SH j ω)
                (ENNReal.ofReal (2 * p)) μ +
              eLpNorm (fun ω => D j ω * F j ω) (ENNReal.ofReal (2 * p)) μ := h_add
        _ ≤ (eLpNorm (fun ω => phi j ω * inner_cH j ω) (ENNReal.ofReal (2 * p)) μ +
              eLpNorm (inner_SH j) (ENNReal.ofReal (2 * p)) μ) +
              eLpNorm (fun ω => D j ω * F j ω) (ENNReal.ofReal (2 * p)) μ := by
          have htemp := add_le_add_right h_sub
            (eLpNorm (fun ω => D j ω * F j ω) (ENNReal.ofReal (2 * p)) μ)
          simpa [add_comm, add_left_comm, add_assoc] using htemp
        _ = eLpNorm (fun ω => phi j ω * inner_cH j ω) (ENNReal.ofReal (2 * p)) μ +
            eLpNorm (inner_SH j) (ENNReal.ofReal (2 * p)) μ +
            eLpNorm (fun ω => D j ω * F j ω) (ENNReal.ofReal (2 * p)) μ := by ring
    have h_bound : eLpNorm (fun ω => phi j ω * inner_cH j ω) (ENNReal.ofReal (2 * p)) μ +
        eLpNorm (inner_SH j) (ENNReal.ofReal (2 * p)) μ +
        eLpNorm (fun ω => D j ω * F j ω) (ENNReal.ofReal (2 * p)) μ ≤
        ENNReal.ofReal (((d : ℝ) * L + (d : ℝ) + 1) * A * B * (a / r)) := by
      have h1 : eLpNorm (fun ω => phi j ω * inner_cH j ω) (ENNReal.ofReal (2 * p)) μ ≤
          ENNReal.ofReal ((d : ℝ) * L * A * B * (a / r)) := h_phi_inner_bound j
      have h2 : eLpNorm (inner_SH j) (ENNReal.ofReal (2 * p)) μ ≤
          ENNReal.ofReal ((d : ℝ) * A * B * (a / r)) := h_inner_SH_bound j
      have h3 : eLpNorm (fun ω => D j ω * F j ω) (ENNReal.ofReal (2 * p)) μ ≤
          ENNReal.ofReal (A * B * (a / r)) := h_DF_bound j
      have hpos1 : 0 ≤ (d : ℝ) * L * A * B * (a / r) := by positivity
      have hpos2 : 0 ≤ (d : ℝ) * A * B * (a / r) := by positivity
      have hpos3 : 0 ≤ A * B * (a / r) := by positivity
      have hsum : ENNReal.ofReal ((d : ℝ) * L * A * B * (a / r)) +
          ENNReal.ofReal ((d : ℝ) * A * B * (a / r)) +
          ENNReal.ofReal (A * B * (a / r)) =
          ENNReal.ofReal (((d : ℝ) * L + (d : ℝ) + 1) * A * B * (a / r)) := by
        calc
          ENNReal.ofReal ((d : ℝ) * L * A * B * (a / r)) +
              ENNReal.ofReal ((d : ℝ) * A * B * (a / r)) +
              ENNReal.ofReal (A * B * (a / r))
            = (ENNReal.ofReal ((d : ℝ) * L * A * B * (a / r)) +
                ENNReal.ofReal ((d : ℝ) * A * B * (a / r))) +
                ENNReal.ofReal (A * B * (a / r)) := by ring
          _ = ENNReal.ofReal (((d : ℝ) * L * A * B * (a / r)) + ((d : ℝ) * A * B * (a / r))) +
                ENNReal.ofReal (A * B * (a / r)) := by
            rw [ENNReal.ofReal_add hpos1 hpos2]
          _ = ENNReal.ofReal ((((d : ℝ) * L * A * B * (a / r)) + ((d : ℝ) * A * B * (a / r))) +
                (A * B * (a / r))) := by
            rw [ENNReal.ofReal_add (by positivity) hpos3]
          _ = ENNReal.ofReal (((d : ℝ) * L + (d : ℝ) + 1) * A * B * (a / r)) := by ring
      rw [← hsum]
      exact add_le_add (add_le_add h1 h2) h3
    exact le_trans h_total h_bound
  -- sum over j
  have hsum_eq : (fun ω => ∑ j, ((phi j ω * ∑ k, c j k ω * H j k ω) -
      (∑ k, S j k ω * H j k ω) + D j ω * F j ω)) =
      (fun ω => ∑ j : Fin d, ((phi j ω * inner_cH j ω) - inner_SH j ω + D j ω * F j ω)) := by
    ext ω
    simp [h_inner_cH_def, h_inner_SH_def]
  rw [hsum_eq]
  have hsum_le : eLpNorm (fun ω => ∑ j : Fin d, ((phi j ω * inner_cH j ω) - inner_SH j ω + D j ω * F j ω))
      (ENNReal.ofReal (2 * p)) μ ≤
      ∑ j : Fin d, eLpNorm (fun ω => (phi j ω * inner_cH j ω) - inner_SH j ω + D j ω * F j ω)
        (ENNReal.ofReal (2 * p)) μ := by
    refine eLpNorm_finset_sum_le (Finset.univ : Finset (Fin d)) _ (fun j _ => ?_) h_one_le_2p
    have hA : AEStronglyMeasurable (fun ω => phi j ω * inner_cH j ω) μ :=
      (h_meas_phi j).mul (h_meas_inner_cH j)
    have hB : AEStronglyMeasurable (inner_SH j) μ := h_meas_inner_SH j
    have hC : AEStronglyMeasurable (fun ω => D j ω * F j ω) μ :=
      (h_meas_D j).mul (h_meas_F j)
    exact (hA.sub hB).add hC
  have hsum_le2 : (∑ j : Fin d, eLpNorm (fun ω => (phi j ω * inner_cH j ω) - inner_SH j ω + D j ω * F j ω)
      (ENNReal.ofReal (2 * p)) μ) ≤
      ∑ j : Fin d, ENNReal.ofReal (((d : ℝ) * L + (d : ℝ) + 1) * A * B * (a / r)) :=
    Finset.sum_le_sum fun j _ => h_single_j_bound j
  have hsum_eq2 : (∑ j : Fin d, ENNReal.ofReal (((d : ℝ) * L + (d : ℝ) + 1) * A * B * (a / r))) =
      (d : ℝ≥0∞) * ENNReal.ofReal (((d : ℝ) * L + (d : ℝ) + 1) * A * B * (a / r)) := by
    simp
  have hfinal : (d : ℝ≥0∞) * ENNReal.ofReal (((d : ℝ) * L + (d : ℝ) + 1) * A * B * (a / r)) =
      ENNReal.ofReal ((((d : ℝ)^2 * (L + 1) + d) * A * B) * (a / r)) := by
    have hd_nonneg : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
    have hx_nonneg : 0 ≤ ((d : ℝ) * L + (d : ℝ) + 1) * A * B * (a / r) := by positivity
    rw [show (d : ℝ≥0∞) = ENNReal.ofReal (d : ℝ) from by simp]
    rw [← ENNReal.ofReal_mul hd_nonneg]
    ring
  calc
    eLpNorm (fun ω => ∑ j : Fin d, ((phi j ω * inner_cH j ω) - inner_SH j ω + D j ω * F j ω))
        (ENNReal.ofReal (2 * p)) μ
      ≤ ∑ j : Fin d, eLpNorm (fun ω => (phi j ω * inner_cH j ω) - inner_SH j ω + D j ω * F j ω)
          (ENNReal.ofReal (2 * p)) μ := hsum_le
    _ ≤ ∑ j : Fin d, ENNReal.ofReal (((d : ℝ) * L + (d : ℝ) + 1) * A * B * (a / r)) := hsum_le2
    _ = (d : ℝ≥0∞) * ENNReal.ofReal (((d : ℝ) * L + (d : ℝ) + 1) * A * B * (a / r)) := hsum_eq2
    _ = ENNReal.ofReal ((((d : ℝ)^2 * (L + 1) + d) * A * B) * (a / r)) := hfinal

end EinsteinRelation.Correctors
