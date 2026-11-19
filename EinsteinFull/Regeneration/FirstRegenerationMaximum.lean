import EinsteinRelation.Regeneration.FirstRegenerationForward
import EinsteinRelation.Regeneration.OneIntervalLocality

/-!
# Maximum before the first regeneration

The geometric step in Gantert–Mathieu–Piatnitski, Lemma 5.8, equation (5.27), controls
past displacement by the first regeneration position. The estimate below uses the
successful bridge's support and a constant sufficient for the tail argument.
-/

open MeasureTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- Every position before the finite first regeneration lies at most `12R` above its
endpoint in the force coordinate, provided the successful bridges stay in their coupling
regions. -/
theorem first_regeneration_past_le_endpoint_add {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (z : CoupledSample d) (i : Fin d)
    (hfin : firstRegenerationTime Δ lam R z i ≠ ⊤)
    (hbridge : ∀ n : ℕ, z.2 n = true → ∀ t : ℝ≥0,
      (n : ℝ≥0) * Δ ≤ t → t ≤ ((n + 1 : ℕ) : ℝ≥0) * Δ →
        z.1 t ∈ couplingRegion i R (z.1 ((n : ℝ≥0) * Δ)))
    (t : ℝ≥0) (ht : t ≤ (firstRegenerationTime Δ lam R z i).toNNReal) :
    z.1 t i ≤ z.1 (firstRegenerationTime Δ lam R z i).toNNReal i + 12 * R := by
  obtain ⟨m, hm⟩ := firstRegenerationTime_eq_succ_grid_of_ne_top Δ hΔ lam R z i hfin
  obtain ⟨hΓ, hb, _⟩ :=
    (firstRegenerationTime_eq_iff_forcedBitTrialEvent Δ hΔ lam R z i m).mp hm
  have hgeom := (forcedBitTrialEvent_geometry Δ hΔ lam R hlam hR i m z hΓ).1
  have hle : (m : ℝ≥0) * Δ ≤ ((m + 1 : ℕ) : ℝ≥0) * Δ :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ m) zero_le
  have hend := (couplingRegion_coordinate_bounds i R _ _ (hbridge m hb _ hle le_rfl)).1
  rw [hm, ENNReal.toNNReal_coe] at ht ⊢
  by_cases hpre : t ≤ (m : ℝ≥0) * Δ
  · have hpast := displacement_le_coordinateMaximum z.1 i t ((m : ℝ≥0) * Δ) hpre
    linarith
  · have hcur := (couplingRegion_coordinate_bounds i R _ _
      (hbridge m hb t (le_of_not_ge hpre) ht)).2
    linarith

/-- The running maximum at the first regeneration is controlled by its displacement. -/
theorem first_regeneration_maximum_le {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (z : CoupledSample d) (i : Fin d)
    (hfin : firstRegenerationTime Δ lam R z i ≠ ⊤)
    (hbridge : ∀ n : ℕ, z.2 n = true → ∀ t : ℝ≥0,
      (n : ℝ≥0) * Δ ≤ t → t ≤ ((n + 1 : ℕ) : ℝ≥0) * Δ →
        z.1 t ∈ couplingRegion i R (z.1 ((n : ℝ≥0) * Δ))) :
    coordinateMaximum z.1 i (firstRegenerationTime Δ lam R z i).toNNReal ≤
      z.1 (firstRegenerationTime Δ lam R z i).toNNReal i - z.1 0 i + 12 * R := by
  apply coordinateMaximum_le
  intro t ht
  have h := first_regeneration_past_le_endpoint_add Δ hΔ lam R hlam hR z i hfin hbridge t ht.2
  linarith

/-- The maximum bound holds almost surely for the supplied annealed split coupling,
conditional only on finiteness of its first regeneration time. -/
theorem ae_first_regeneration_maximum_le {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (i : Fin d) (hsupport : HasSuccessfulBridgeSupport Q Δ i R K) :
    ∀ᵐ ωz ∂annealedCoupledLaw Q K,
      firstRegenerationTime Δ lam R ωz.2 i ≠ ⊤ →
        coordinateMaximum ωz.2.1 i (firstRegenerationTime Δ lam R ωz.2 i).toNNReal ≤
          ωz.2.1 (firstRegenerationTime Δ lam R ωz.2 i).toNNReal i - ωz.2.1 0 i + 12 * R := by
  have hτ := (measurable_firstRegenerationTime Δ lam R i).comp
    (measurable_snd : Measurable (Prod.snd : FieldPair d × CoupledSample d → _))
  have hpath : Measurable (fun ωz : FieldPair d × CoupledSample d => ωz.2.1) :=
    measurable_snd.fst
  have hmax := (measurable_coordinateMaximum i).comp (hτ.ennreal_toNNReal.prodMk hpath)
  have hx := measurable_path_eval.comp (hτ.ennreal_toNNReal.prodMk hpath)
  have hx0 : Measurable (fun ωz : FieldPair d × CoupledSample d => ωz.2.1 0 i) :=
    (measurable_pi_apply i).comp ((continuous_eval_const (0 : ℝ≥0)).measurable.comp hpath)
  have hm : MeasurableSet {ωz : FieldPair d × CoupledSample d |
      firstRegenerationTime Δ lam R ωz.2 i ≠ ⊤ →
        coordinateMaximum ωz.2.1 i (firstRegenerationTime Δ lam R ωz.2 i).toNNReal ≤
          ωz.2.1 (firstRegenerationTime Δ lam R ωz.2 i).toNNReal i - ωz.2.1 0 i + 12 * R} :=
    (hτ (measurableSet_singleton ⊤)).compl.imp
      (measurableSet_le hmax ((((measurable_pi_apply i).comp hx).sub hx0).add_const _))
  apply Measure.ae_compProd_of_ae_ae hm
  filter_upwards [hK.1, hsupport.1] with ω hprob hsupp
  have : IsProbabilityMeasure (originCoupledLaw K ω) := hprob
  rw [Probability.probabilityPart_eq_of_isProbabilityMeasure (originCoupledLaw K) ω]
  filter_upwards [hsupp] with z hz
  exact fun hfin => first_regeneration_maximum_le Δ hΔ lam R hlam hR z i hfin hz

end EinsteinFull.Regeneration
