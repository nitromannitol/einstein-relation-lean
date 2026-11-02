import EinsteinRelation.Regeneration.NoBacktrackingPrefix
import EinsteinRelation.Regeneration.FirstRegenerationFiniteness
import EinsteinRelation.Regeneration.RestrictedRecordShift

/-!
# Forward displacement at the first regeneration time

Source `paper/main.tex:412–425`. The successful bridge starts at height at
least `2R` and stays above its starting height minus `R`. In particular, its
endpoint has positive displacement, so translating the restricted future
field there remains inside the old future half-space.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinRelation.Regeneration

/-- The first-regeneration endpoint is forward of the initial point on every
finite slice with successful-bridge support (`paper/main.tex:412–425`). -/
theorem firstRegenerationTime_forward_of_bridge {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (z : CoupledSample d) (i : Fin d)
    (hfin : firstRegenerationTime Δ lam R z i ≠ ⊤)
    (hbridge : ∀ n : ℕ, z.2 n = true → ∀ t : ℝ≥0,
      (n : ℝ≥0) * Δ ≤ t → t ≤ ((n + 1 : ℕ) : ℝ≥0) * Δ →
        z.1 t ∈ couplingRegion i R (z.1 ((n : ℝ≥0) * Δ))) :
    0 ≤ z.1 (firstRegenerationTime Δ lam R z i).toNNReal i - z.1 0 i := by
  obtain ⟨m, hm⟩ := firstRegenerationTime_eq_succ_grid_of_ne_top Δ hΔ lam R z i hfin
  obtain ⟨hΓ, hb, _⟩ :=
    (firstRegenerationTime_eq_iff_forcedBitTrialEvent Δ hΔ lam R z i m).mp hm
  have hh := (forcedBitTrialEvent_geometry Δ hΔ lam R hlam hR i m z hΓ).2
  have hle : (m : ℝ≥0) * Δ ≤ ((m + 1 : ℕ) : ℝ≥0) * Δ :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ m) zero_le
  have hend := hbridge m hb _ hle le_rfl
  have hnorm := coordinate_abs_le_euclideanNorm
    (z.1 (((m + 1 : ℕ) : ℝ≥0) * Δ) -
      (z.1 ((m : ℝ≥0) * Δ) + (5 * R) • unitVector i)) i
  have hlow := (abs_lt.mp (hnorm.trans_lt hend)).1
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, unitVector, Pi.single_eq_same,
    smul_eq_mul, mul_one] at hlow
  rw [hm, ENNReal.toNNReal_coe]
  linarith

/-- Under the actual annealed coupling, finiteness and successful-bridge
support imply forward displacement (`paper/main.tex:412–425`). -/
theorem ae_firstRegenerationTime_forward {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (i : Fin d) (hsupport : HasSuccessfulBridgeSupport Q Δ i R K) :
    ∀ᵐ ωz ∂annealedCoupledLaw Q K,
      firstRegenerationTime Δ lam R ωz.2 i ≠ ⊤ →
        0 ≤ ωz.2.1 (firstRegenerationTime Δ lam R ωz.2 i).toNNReal i - ωz.2.1 0 i := by
  have hτ := (measurable_firstRegenerationTime Δ lam R i).comp
    (measurable_snd : Measurable (Prod.snd : FieldPair d × CoupledSample d → _))
  have hx := measurable_path_eval.comp (hτ.ennreal_toNNReal.prodMk measurable_snd.fst)
  have hx0 : Measurable (fun ωz : FieldPair d × CoupledSample d => ωz.2.1 0 i) :=
    (measurable_pi_apply i).comp
      ((continuous_eval_const (0 : ℝ≥0)).measurable.comp measurable_snd.fst)
  have hm : MeasurableSet {ωz : FieldPair d × CoupledSample d |
      firstRegenerationTime Δ lam R ωz.2 i ≠ ⊤ →
        0 ≤ ωz.2.1 (firstRegenerationTime Δ lam R ωz.2 i).toNNReal i - ωz.2.1 0 i} :=
    (hτ (measurableSet_singleton ⊤)).compl.imp
    (measurableSet_le measurable_const (((measurable_pi_apply i).comp hx).sub hx0))
  apply Measure.ae_compProd_of_ae_ae hm
  filter_upwards [hK.1, hsupport.1] with ω hprob hsupp
  haveI : IsProbabilityMeasure (originCoupledLaw K ω) := hprob
  rw [Probability.probabilityPart_eq_of_isProbabilityMeasure (originCoupledLaw K) ω]
  filter_upwards [hsupp] with z hz
  exact fun hfin => firstRegenerationTime_forward_of_bridge Δ hΔ lam R hlam hR z i hfin hz


end EinsteinRelation.Regeneration
