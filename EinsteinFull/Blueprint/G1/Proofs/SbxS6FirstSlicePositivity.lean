import EinsteinFull.Work.W1.GMPKilledSemigroupSupport
import EinsteinFull.Blueprint.Foundation.Proofs.SbxS1PastKernel
import EinsteinRelation.TimeChange.EuclideanTransport
import EinsteinRelation.Probability.FiniteHistoryMeasurability
import EinsteinRelation.Regeneration.RenewalCarriers
import EinsteinRelation.Regeneration.FreshEventMass
import EinsteinFull.Blueprint.Foundation.Proofs.W1Queue0330_1
import EinsteinFull.Blueprint.G1.Proofs.SbxS6ConditionIterate
import EinsteinRelation.Regeneration.FirstRegenerationSliceFubini
import EinsteinRelation.Regeneration.ForcedBitSlice
import EinsteinRelation.Regeneration.Chronology
import Mathlib.Topology.CompactOpen
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import PDEFoundation.Sobolev.H1.LevelSets
import PDEFoundation.Sobolev.W1p.ZeroGradient
import PDEFoundation.Sobolev.Trace.Density.Glue
import Mathlib.Tactic.Linter
import Mathlib.Analysis.Analytic.Uniqueness

/-!
Continuous-block mesh support for the first Gamma₂ slice, paper/main.tex:356–375.
The restart and product estimates below concern the actual GMP path law. Their
one-step inequalities are explicit analytic discharge sites, not extra graph
dependencies or a proof of the condition-iterate root.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal InnerProductSpace

namespace EinsteinFull.Blueprint.FirstSlicePositivity

-- Keep the matrix measurable instance used by the regeneration records.
attribute [local instance 2000] EinsteinRelation.instMeasurableSpaceMat
open EinsteinRelation
open EinsteinRelation.External.GantertSection7Support

noncomputable section

theorem continuous_euclideanNorm {d : ℕ} :
    Continuous (fun x : Vec d => euclideanNorm x) := by
  unfold euclideanNorm euclideanSq dot
  exact Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ =>
    (continuous_apply i).mul (continuous_apply i))

/-- A spatial ball in the force-scaled Euclidean coordinates of the mesh. -/
def meshBall {d : ℕ} (lam radius : ℝ) (center : Vec d) : Set (Vec d) :=
  {x | euclideanNorm (lam • x - center) < radius}

theorem isOpen_meshBall {d : ℕ} (lam radius : ℝ) (center : Vec d) :
    IsOpen (meshBall lam radius center) :=
  isOpen_lt (continuous_euclideanNorm.comp
    ((continuous_const.fun_smul continuous_id).sub continuous_const)) continuous_const

/-- A complete closed time block and its small entrance ball for the next block. -/
def meshPiece {d : ℕ} (lam ε : ℝ) (τ : ℝ≥0) (c : ℕ → Vec d)
    (k : ℕ) : Set (Path d) :=
  {Y | (∀ s : ℝ≥0, s ≤ τ → euclideanNorm (lam • Y s - c k) < ε / 2) ∧
    euclideanNorm (lam • Y τ - c (k + 1)) < ε / 16}

/-- Positive force converts a scaled mesh ball to its literal physical ball. -/
theorem meshBall_eq_unscaled {d : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (radius : ℝ) (center : Vec d) :
    meshBall lam radius center =
      {x | euclideanNorm (x - lam⁻¹ • center) < radius / lam} := by
  ext x
  have hscale : lam • (x - lam⁻¹ • center) = lam • x - center := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hlam.ne', one_smul]
  change euclideanNorm (lam • x - center) < radius ↔
    euclideanNorm (x - lam⁻¹ • center) < radius / lam
  rw [← hscale, TimeChange.euclideanNorm_smul, abs_of_pos hlam,
    lt_div_iff₀ hlam, mul_comm]

/-- The mesh domain is the literal round ball in the installed coordinate
Sobolev API, with the same Euclidean norm and physical radius. -/
theorem meshBall_eq_pdeEuclideanBall {d : ℕ} {lam radius : ℝ}
    (hlam : 0 < lam) (hradius : 0 < radius) (center : Vec d) :
    meshBall lam radius center = PDE.euclideanBall (lam⁻¹ • center) (radius / lam) := by
  rw [meshBall_eq_unscaled hlam]
  ext x
  exact (PDE.mem_euclideanBall_iff_vecEuclideanNorm_lt (div_pos hradius hlam)).symm

/-- The genuine mesh killing domain has the connected convex Sobolev geometry. -/
theorem meshBall_isOpenBoundedConvexDomain {d : ℕ} {lam radius : ℝ}
    (hlam : 0 < lam) (hradius : 0 < radius) (center : Vec d) :
    PDE.IsOpenBoundedConvexDomain (meshBall lam radius center) := by
  rw [meshBall_eq_pdeEuclideanBall hlam hradius center]
  exact PDE.isOpenBoundedConvexDomain_euclideanBall _ (div_pos hradius hlam)

/-- The center is fixed throughout the closed block; only the terminal
ball uses the next center. This is an equality of actual path events. -/
theorem meshPiece_eq_unscaled {d : ℕ} {lam : ℝ} (hlam : 0 < lam)
    (ε : ℝ) (τ : ℝ≥0) (c : ℕ → Vec d) (k : ℕ) :
    meshPiece lam ε τ c k =
      {Y | (∀ s : ℝ≥0, s ≤ τ →
        euclideanNorm (Y s - lam⁻¹ • c k) < (ε / 2) / lam) ∧
        euclideanNorm (Y τ - lam⁻¹ • c (k + 1)) < (ε / 16) / lam} := by
  have hball (radius : ℝ) (center x : Vec d) :
      euclideanNorm (lam • x - center) < radius ↔
        euclideanNorm (x - lam⁻¹ • center) < radius / lam :=
    Set.ext_iff.mp (meshBall_eq_unscaled hlam radius center) x
  ext Y
  simp only [meshPiece, Set.mem_ofPred_eq, hball]

/-- Closed confinement includes the starting point, without a time-null exception. -/
theorem meshPiece_start {d : ℕ} {lam ε : ℝ} {τ : ℝ≥0}
    {c : ℕ → Vec d} {k : ℕ} {Y : Path d} (hY : Y ∈ meshPiece lam ε τ c k) :
    Y 0 ∈ meshBall lam (ε / 2) (c k) :=
  hY.1 0 bot_le

/-- Closed confinement and the smaller endpoint requirement both hold at the endpoint. -/
theorem meshPiece_endpoint {d : ℕ} {lam ε : ℝ} {τ : ℝ≥0}
    {c : ℕ → Vec d} {k : ℕ} {Y : Path d} (hY : Y ∈ meshPiece lam ε τ c k) :
    Y τ ∈ meshBall lam (ε / 2) (c k) ∩ meshBall lam (ε / 16) (c (k + 1)) :=
  ⟨hY.1 τ le_rfl, hY.2⟩

/-- A zero-length block retains both its entrance and terminal conditions. -/
theorem meshPiece_zero {d : ℕ} (lam ε : ℝ) (c : ℕ → Vec d) (k : ℕ) :
    meshPiece lam ε 0 c k =
      {Y | Y 0 ∈ meshBall lam (ε / 2) (c k) ∩
        meshBall lam (ε / 16) (c (k + 1))} := by
  ext Y
  constructor
  · exact meshPiece_endpoint
  · rintro ⟨hstart, hend⟩
    exact ⟨fun s hs => (nonpos_iff_eq_zero.mp hs) ▸ hstart, hend⟩

/-- Exact Lebesgue volume of a translated force-scaled Euclidean ball.
The carrier still has its original coordinate norm; the volume computation
uses the measure-preserving Euclidean transport only inside this proof. -/
theorem volume_meshBall {d : ℕ} (hd : 0 < d) {lam : ℝ} (hlam : 0 < lam)
    (radius : ℝ) (center : Vec d) :
    volume (meshBall lam radius center) =
      ENNReal.ofReal (radius / lam) ^ d *
        ENNReal.ofReal (Real.sqrt Real.pi ^ d / Real.Gamma ((d : ℝ) / 2 + 1)) := by
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  rw [meshBall_eq_unscaled hlam]
  have heq : {x : Vec d | euclideanNorm (x - lam⁻¹ • center) < radius / lam} =
      WithLp.toLp 2 ⁻¹' Metric.ball
        (WithLp.toLp 2 (lam⁻¹ • center) : EuclideanSpace ℝ (Fin d)) (radius / lam) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Metric.mem_ball, dist_eq_norm,
      ← WithLp.toLp_sub, ← TimeChange.euclideanNorm_eq_norm_toLp]
  rw [heq, (PiLp.volume_preserving_toLp (Fin d)).measure_preimage measurableSet_ball.nullMeasurableSet,
    EuclideanSpace.volume_ball]
  simp only [Fintype.card_fin]

/-- The mesh terminal radius is exactly `l / (512 * lam)` in physical space. -/
theorem volume_meshTerminalBall {d : ℕ} (hd : 0 < d) {lam : ℝ} (hlam : 0 < lam)
    (l : ℝ) (center : Vec d) :
    volume (meshBall lam ((l / 32) / 16) center) =
      ENNReal.ofReal (l / (512 * lam)) ^ d *
        ENNReal.ofReal (Real.sqrt Real.pi ^ d / Real.Gamma ((d : ℝ) / 2 + 1)) := by
  have hr : ((l / 32) / 16) / lam = l / (512 * lam) := by
    simp only [div_div]
    norm_num
  simpa only [hr] using volume_meshBall hd hlam ((l / 32) / 16) center

/-- A positive-radius physical mesh ball has strictly positive Lebesgue mass. -/
theorem volume_meshBall_pos {d : ℕ} {lam radius : ℝ} (hlam : 0 < lam)
    (hradius : 0 < radius) (center : Vec d) :
    0 < volume (meshBall lam radius center) := by
  apply (isOpen_meshBall lam radius center).measure_pos volume
  refine ⟨lam⁻¹ • center, ?_⟩
  change euclideanNorm (lam • (lam⁻¹ • center) - center) < radius
  simpa only [smul_smul, mul_inv_cancel₀ hlam.ne', one_smul, sub_self,
    TimeChange.euclideanNorm_eq_norm_toLp, WithLp.toLp_zero, norm_zero] using hradius

/-- Translation of a force-scaled Euclidean ball does not change its volume. -/
theorem volume_meshBall_eq {d : ℕ} (hd : 0 < d) {lam : ℝ} (hlam : 0 < lam)
    (radius : ℝ) (center : Vec d) :
    volume (meshBall lam radius center) = volume (meshBall lam radius (0 : Vec d)) := by
  rw [volume_meshBall hd hlam, volume_meshBall hd hlam]

/-- The first m continuous blocks, observed at their original time scale. -/
def meshPrefix {d : ℕ} (lam ε : ℝ) (τ : ℝ≥0) (c : ℕ → Vec d)
    (m : ℕ) : Set (Path d) :=
  {Y | ∀ k : ℕ, k < m → gmpShiftPath ((k : ℝ≥0) * τ) Y ∈ meshPiece lam ε τ c k}

theorem measurableSet_meshPiece {d : ℕ} (lam ε : ℝ) (τ : ℝ≥0)
    (c : ℕ → Vec d) (k : ℕ) : MeasurableSet (meshPiece lam ε τ c k) := by
  let F : Path d → C(ℝ≥0, ℝ) := fun Y =>
    ⟨fun s => euclideanNorm (lam • Y s - c k),
      continuous_euclideanNorm.comp ((continuous_const.fun_smul Y.continuous).sub
        continuous_const)⟩
  have hF : Continuous F := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact continuous_euclideanNorm.comp
      ((continuous_const.fun_smul continuous_eval).sub continuous_const)
  have hblock := (ContinuousMap.isOpen_setOfPred_mapsTo
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ≥0) τ))
    (isOpen_Iio : IsOpen (Set.Iio (ε / 2)))).preimage hF
  have hend : Continuous (fun Y : Path d => euclideanNorm (lam • Y τ - c (k + 1))) :=
    continuous_euclideanNorm.comp
      ((continuous_const.fun_smul (continuous_eval_const τ)).sub continuous_const)
  have heq : meshPiece lam ε τ c k =
      (F ⁻¹' {f | Set.MapsTo f (Set.Icc 0 τ) (Set.Iio (ε / 2))}) ∩
        {Y | euclideanNorm (lam • Y τ - c (k + 1)) < ε / 16} := by
    ext Y
    simp only [meshPiece, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage,
      Set.MapsTo, Set.mem_Icc, Set.mem_Iio, F, ContinuousMap.coe_mk, zero_le, true_and]
  rw [heq]
  exact hblock.measurableSet.inter (hend.measurable measurableSet_Iio)

theorem meshPrefix_zero {d : ℕ} (lam ε : ℝ) (τ : ℝ≥0) (c : ℕ → Vec d) :
    meshPrefix lam ε τ c 0 = Set.univ := by
  ext Y
  simp only [meshPrefix, Set.mem_ofPred_eq, not_lt_zero, IsEmpty.forall_iff,
    implies_true, Set.mem_univ]

theorem meshPrefix_succ {d : ℕ} (lam ε : ℝ) (τ : ℝ≥0) (c : ℕ → Vec d) (m : ℕ) :
    meshPrefix lam ε τ c (m + 1) = meshPrefix lam ε τ c m ∩
      (gmpShiftPath ((m : ℝ≥0) * τ)) ⁻¹' meshPiece lam ε τ c m := by
  ext Y
  change (∀ k, k < m + 1 → _) ↔ (∀ k, k < m → _) ∧ _
  constructor
  · intro h
    exact ⟨fun k hk => h k (by omega), h m (by omega)⟩
  · rintro ⟨h, hm⟩ k hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact h k hk
    · exact hm

theorem measurableSet_meshPrefix {d : ℕ} (lam ε : ℝ) (τ : ℝ≥0)
    (c : ℕ → Vec d) (m : ℕ) : MeasurableSet (meshPrefix lam ε τ c m) := by
  induction m with
  | zero => rw [meshPrefix_zero]; exact MeasurableSet.univ
  | succ m ih =>
    rw [meshPrefix_succ]
    exact ih.inter ((measurableSet_meshPiece lam ε τ c m).preimage
      (measurable_gmpShiftPath _))

theorem meshPiece_congr {d : ℕ} (lam ε : ℝ) (τ : ℝ≥0) (c : ℕ → Vec d)
    (k : ℕ) {Y Z : Path d} (h : ∀ s ≤ τ, Y s = Z s) :
    Y ∈ meshPiece lam ε τ c k ↔ Z ∈ meshPiece lam ε τ c k := by
  change ((∀ s ≤ τ, _) ∧ _) ↔ ((∀ s ≤ τ, _) ∧ _)
  rw [h τ le_rfl]
  apply and_congr_left
  intro _
  apply forall_congr'
  intro s
  apply forall_congr'
  intro hs
  rw [h s hs]

/-- Clamping after the last mesh time preserves every all-time block constraint. -/
theorem meshPrefix_prefix {d : ℕ} (lam ε : ℝ) (τ : ℝ≥0)
    (c : ℕ → Vec d) (m : ℕ) :
    (gmpPrefixPath ((m : ℝ≥0) * τ)) ⁻¹' meshPrefix lam ε τ c m =
      meshPrefix lam ε τ c m := by
  ext Y
  change (∀ k, k < m → _) ↔ (∀ k, k < m → _)
  apply forall_congr'
  intro k
  apply forall_congr'
  intro hk
  apply meshPiece_congr
  intro s hs
  have ht : (k : ℝ≥0) * τ + s ≤ (m : ℝ≥0) * τ := calc
    (k : ℝ≥0) * τ + s ≤ (k : ℝ≥0) * τ + τ := add_le_add le_rfl hs
    _ = ((k + 1 : ℕ) : ℝ≥0) * τ := by rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    _ ≤ (m : ℝ≥0) * τ := mul_le_mul_of_nonneg_right (by exact_mod_cast hk) zero_le
  change Y (min ((k : ℝ≥0) * τ + s) ((m : ℝ≥0) * τ)) = Y _
  rw [min_eq_left ht]

theorem measurableSet_meshPrefix_past {d : ℕ} (lam ε : ℝ) (τ : ℝ≥0)
    (c : ℕ → Vec d) (m : ℕ) :
    MeasurableSet[gmpPastSigma ((m : ℝ≥0) * τ)] (meshPrefix lam ε τ c m) := by
  rw [← comap_gmpPrefixPath_eq_gmpPastSigma]
  exact ⟨_, measurableSet_meshPrefix lam ε τ c m, meshPrefix_prefix lam ε τ c m⟩

/-- Closed blocks cover their full time window, including its right endpoint. -/
theorem exists_mesh_interval (τ : ℝ≥0) (N : ℕ) (hN : 0 < N)
    (s : ℝ≥0) (hs : s ≤ (N : ℝ≥0) * τ) :
    ∃ k : ℕ, k < N ∧ (k : ℝ≥0) * τ ≤ s ∧ s ≤ ((k + 1 : ℕ) : ℝ≥0) * τ := by
  induction N with
  | zero => omega
  | succ N ih =>
    by_cases hzero : N = 0
    · subst N
      exact ⟨0, by omega, by simp only [Nat.cast_zero, zero_mul, zero_le], hs⟩
    · by_cases hpre : s ≤ (N : ℝ≥0) * τ
      · obtain ⟨k, hk, hleft, hright⟩ := ih (by omega) hpre
        exact ⟨k, by omega, hleft, hright⟩
      · exact ⟨N, by omega, (lt_of_not_ge hpre).le, hs⟩

/-- The actual polygonal Gamma₂ of the paper. -/
def tubeCurve {d : ℕ} (i : Fin d) (l : ℝ) (u : ℝ) : Vec d :=
  min ((25 * l / 4) * u) (25 * l / 8) • unitVector i

theorem continuous_tubeCurve {d : ℕ} (i : Fin d) (l : ℝ) :
    Continuous (tubeCurve i l) :=
  ((continuous_const.mul continuous_id).min continuous_const).smul continuous_const

/-- The first tube is an all-time strict Euclidean event. -/
def tubeEvent {d : ℕ} (i : Fin d) (lam l : ℝ) : Set (Path d) :=
  {Y | ∀ u : ℝ≥0, (u : ℝ) ≤ 1 →
    euclideanNorm (lam • Y ((u : ℝ) / lam ^ 2).toNNReal - tubeCurve i l u) < l / 32}

theorem measurableSet_tubeEvent {d : ℕ} (i : Fin d) (lam l : ℝ) :
    MeasurableSet (tubeEvent i lam l) := by
  let F : Path d → C(ℝ≥0, ℝ) := fun Y =>
    ⟨fun u => euclideanNorm
      (lam • Y ((u : ℝ) / lam ^ 2).toNNReal - tubeCurve i l u),
      continuous_euclideanNorm.comp ((continuous_const.fun_smul
        (Y.continuous.comp (continuous_real_toNNReal.comp
          (NNReal.continuous_coe.div_const _)))).sub
        ((continuous_tubeCurve i l).comp NNReal.continuous_coe))⟩
  have hF : Continuous F := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact continuous_euclideanNorm.comp ((continuous_const.fun_smul
      (continuous_eval.comp (continuous_fst.prodMk (continuous_real_toNNReal.comp
        ((NNReal.continuous_coe.comp continuous_snd).div_const _))))).sub
      ((continuous_tubeCurve i l).comp (NNReal.continuous_coe.comp continuous_snd)))
  have ho := (ContinuousMap.isOpen_setOfPred_mapsTo
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ≥0) 1))
    (isOpen_Iio : IsOpen (Set.Iio (l / 32)))).preimage hF
  have heq : tubeEvent i lam l =
      F ⁻¹' {f | Set.MapsTo f (Set.Icc 0 1) (Set.Iio (l / 32))} := by
    ext Y
    simp only [tubeEvent, Set.mem_ofPred_eq, Set.mem_preimage, Set.MapsTo,
      Set.mem_Icc, Set.mem_Iio, F, ContinuousMap.coe_mk, zero_le, true_and]
    exact ⟨fun h u hu => h u (by exact_mod_cast hu),
      fun h u hu => h (by exact_mod_cast hu)⟩
  rw [heq]
  exact ho.measurableSet

/-- The lifted tube reads only the path through Δ and no Bernoulli bit. -/
theorem measurableSet_tubeEvent_history {d : ℕ} (i : Fin d) (lam l : ℝ) :
    MeasurableSet[Regeneration.finiteHistorySigma (Regeneration.Renewal.regenDelta lam) 1]
      {z : Regeneration.CoupledSample d | z.1 ∈ tubeEvent i lam l} := by
  let A : Set (Regeneration.CoupledSample d) := {z | z.1 ∈ tubeEvent i lam l}
  have hA : MeasurableSet A := (measurableSet_tubeEvent i lam l).preimage measurable_fst
  have heq : (Probability.stoppedHistorySample (Regeneration.Renewal.regenDelta lam) 1) ⁻¹' A = A := by
    ext z
    change (∀ u : ℝ≥0, (u : ℝ) ≤ 1 → _) ↔ (∀ u : ℝ≥0, (u : ℝ) ≤ 1 → _)
    apply forall_congr'
    intro u
    apply forall_congr'
    intro hu
    rw [Probability.stoppedHistorySample_path]
    simp only [Nat.cast_one, one_mul, Regeneration.Renewal.regenDelta]
    apply Real.toNNReal_le_toNNReal
    simpa only [div_eq_mul_inv, one_mul] using
      mul_le_mul_of_nonneg_right hu (inv_nonneg.mpr (sq_nonneg lam))
  change MeasurableSet[Regeneration.finiteHistorySigma (Regeneration.Renewal.regenDelta lam) 1] A
  rw [← heq]
  exact hA.preimage (Probability.measurable_stoppedHistorySample _ _)

theorem euclideanNorm_unitVector {d : ℕ} (i : Fin d) :
    euclideanNorm (unitVector i) = 1 := by
  simp [euclideanNorm, euclideanSq, dot, unitVector, Pi.single_apply, mul_ite]

theorem tubeCurve_dist_le {d : ℕ} (i : Fin d) {l : ℝ} (hl : 0 ≤ l) (u v : ℝ) :
    euclideanNorm (tubeCurve i l u - tubeCurve i l v) ≤ (25 * l / 4) * |u - v| := by
  unfold tubeCurve
  rw [← sub_smul, TimeChange.euclideanNorm_smul, euclideanNorm_unitVector, mul_one]
  have h := abs_min_sub_min_le_max ((25 * l / 4) * u) (25 * l / 8)
    ((25 * l / 4) * v) (25 * l / 8)
  have hcoef : 0 ≤ 25 * l / 4 := by positivity
  simpa only [sub_self, abs_zero, ← mul_sub, abs_mul, abs_of_nonneg hcoef,
    max_eq_left (mul_nonneg hcoef (abs_nonneg (u - v)))] using h

/-- The mesh size makes the curve motion on one block at most ε/16. -/
theorem tubeCurve_mesh_dist {d : ℕ} (i : Fin d) {l : ℝ} (hl : 0 ≤ l)
    (k : ℕ) (u : ℝ) (hleft : (k : ℝ) / 3200 ≤ u)
    (hright : u ≤ (k + 1 : ℕ) / 3200) :
    euclideanNorm (tubeCurve i l u - tubeCurve i l ((k : ℝ) / 3200)) ≤ (l / 32) / 16 := by
  have h := tubeCurve_dist_le i hl u ((k : ℝ) / 3200)
  rw [abs_of_nonneg (sub_nonneg.mpr hleft)] at h
  have hwidth : u - (k : ℝ) / 3200 ≤ (1 : ℝ) / 3200 := by
    push_cast at hright
    linarith only [hright]
  have hmul := mul_le_mul_of_nonneg_left hwidth (show 0 ≤ 25 * l / 4 by positivity)
  exact h.trans (by nlinarith only [hmul])

/-- The mesh increment in the original, unscaled path clock. -/
def tubeStepTime (lam : ℝ) : ℝ≥0 := ((1 : ℝ) / 3200 / lam ^ 2).toNNReal

/-- Curve centres at the fixed 3200-point mesh. -/
def tubeCenters {d : ℕ} (i : Fin d) (l : ℝ) (k : ℕ) : Vec d :=
  tubeCurve i l ((k : ℝ) / 3200)

theorem coe_tubeStepTime (lam : ℝ) :
    (tubeStepTime lam : ℝ) = (1 : ℝ) / 3200 / lam ^ 2 := by
  exact Real.coe_toNNReal _ (div_nonneg (by norm_num) (sq_nonneg lam))

theorem tubeStepTime_pos {lam : ℝ} (hlam : 0 < lam) : 0 < tubeStepTime lam :=
  Real.toNNReal_pos.mpr (div_pos (by norm_num) (sq_pos_of_pos hlam))

theorem tubeStepTime_total (lam : ℝ) :
    (3200 : ℝ≥0) * tubeStepTime lam = Regeneration.Renewal.regenDelta lam := by
  apply NNReal.coe_injective
  rw [NNReal.coe_mul, coe_tubeStepTime]
  change (3200 : ℝ) * (1 / 3200 / lam ^ 2) = ((lam ^ 2)⁻¹.toNNReal : ℝ)
  rw [Real.coe_toNNReal _ (inv_nonneg.mpr (sq_nonneg lam))]
  ring

/-- Every terminal mesh ball lies strictly inside its current killing ball.
This holds at the original scale, for every mesh index. -/
theorem meshTerminalBall_subset_domain {d : ℕ} (i : Fin d) {l : ℝ} (hl : 0 < l)
    (lam : ℝ) (k : ℕ) :
    meshBall lam ((l / 32) / 16) (tubeCenters i l (k + 1)) ⊆
      meshBall lam ((l / 32) / 2) (tubeCenters i l k) := by
  intro x hx
  have hc := tubeCurve_mesh_dist i hl.le k ((k + 1 : ℕ) / 3200)
    (by push_cast; linarith) le_rfl
  have htri := TimeChange.euclideanNorm_add_le
    (lam • x - tubeCenters i l (k + 1))
    (tubeCenters i l (k + 1) - tubeCenters i l k)
  rw [sub_add_sub_cancel] at htri
  change euclideanNorm (lam • x - tubeCenters i l (k + 1)) < (l / 32) / 16 at hx
  change euclideanNorm (tubeCenters i l (k + 1) - tubeCenters i l k) ≤
    (l / 32) / 16 at hc
  change euclideanNorm (lam • x - tubeCenters i l k) < (l / 32) / 2
  linarith only [htri, hx, hc, hl]

theorem tubeCenters_zero {d : ℕ} (i : Fin d) {l : ℝ} (hl : 0 ≤ l) :
    tubeCenters i l 0 = 0 := by
  simp only [tubeCenters, tubeCurve, Nat.cast_zero, zero_div, mul_zero,
    min_eq_left (show 0 ≤ 25 * l / 8 by positivity), zero_smul]

theorem tubeCenters_origin_mem {d : ℕ} (i : Fin d) (lam : ℝ)
    {l : ℝ} (hl : 0 < l) :
    euclideanNorm (lam • (0 : Vec d) - tubeCenters i l 0) < (l / 32) / 16 := by
  rw [tubeCenters_zero i hl.le, smul_zero, sub_zero]
  simp only [euclideanNorm, euclideanSq, dot, Pi.zero_apply, zero_mul,
    Finset.sum_const_zero, Real.sqrt_zero]
  positivity

/-- No finite-dimensional cylinder replacement: every time in [0,Δ] is controlled. -/
theorem meshPrefix_subset_tubeEvent {d : ℕ} (i : Fin d) {lam l : ℝ}
    (hlam : 0 < lam) (hl : 0 < l) :
    meshPrefix lam (l / 32) (tubeStepTime lam) (tubeCenters i l) 3200 ⊆
      tubeEvent i lam l := by
  intro Y hY u hu
  let s : ℝ≥0 := ((u : ℝ) / lam ^ 2).toNNReal
  have hsq : 0 < lam ^ 2 := sq_pos_of_pos hlam
  have hscoe : (s : ℝ) = (u : ℝ) / lam ^ 2 :=
    Real.coe_toNNReal _ (div_nonneg u.coe_nonneg hsq.le)
  have hsend : (s : ℝ) * lam ^ 2 = u := by
    rw [hscoe, div_mul_cancel₀ _ (ne_of_gt hsq)]
  have hs : s ≤ (3200 : ℝ≥0) * tubeStepTime lam := by
    rw [tubeStepTime_total lam]
    change ((u : ℝ) / lam ^ 2).toNNReal ≤ ((lam ^ 2)⁻¹).toNNReal
    apply Real.toNNReal_le_toNNReal
    simpa only [one_div] using div_le_div_of_nonneg_right hu hsq.le
  obtain ⟨k, hk, hleft, hright⟩ := exists_mesh_interval (tubeStepTime lam) 3200
    (by norm_num) s hs
  let v := s - (k : ℝ≥0) * tubeStepTime lam
  have hv : v ≤ tubeStepTime lam := by
    apply tsub_le_iff_left.mpr
    simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using hright
  have hkv : (k : ℝ≥0) * tubeStepTime lam + v = s := add_tsub_cancel_of_le hleft
  have hblock := (hY k hk).1 v hv
  change euclideanNorm (lam • Y ((k : ℝ≥0) * tubeStepTime lam + v) -
    tubeCenters i l k) < (l / 32) / 2 at hblock
  rw [hkv] at hblock
  have hgrid (j : ℕ) : (j : ℝ) * (tubeStepTime lam : ℝ) * lam ^ 2 = (j : ℝ) / 3200 := by
    rw [coe_tubeStepTime]
    field_simp [ne_of_gt hlam]
  have hleft' : (k : ℝ) / 3200 ≤ (u : ℝ) := by
    have hle := mul_le_mul_of_nonneg_right (show (k : ℝ) * (tubeStepTime lam : ℝ) ≤ s by
      exact_mod_cast hleft) hsq.le
    rwa [hgrid, hsend] at hle
  have hright' : (u : ℝ) ≤ (k + 1 : ℕ) / 3200 := by
    have hle := mul_le_mul_of_nonneg_right
      (show (s : ℝ) ≤ ((k + 1 : ℕ) : ℝ) * (tubeStepTime lam : ℝ) by
        exact_mod_cast hright) hsq.le
    rwa [hgrid, hsend] at hle
  have hcurve := tubeCurve_mesh_dist i hl.le k u hleft' hright'
  have hnorm : euclideanNorm (lam • Y s - tubeCurve i l u) ≤
      euclideanNorm (lam • Y s - tubeCenters i l k) +
        euclideanNorm (tubeCurve i l u - tubeCenters i l k) := by
    have htriangle := TimeChange.euclideanNorm_add_le
      (lam • Y s - tubeCenters i l k) (tubeCenters i l k - tubeCurve i l u)
    have hneg : euclideanNorm (tubeCenters i l k - tubeCurve i l u) =
        euclideanNorm (tubeCurve i l u - tubeCenters i l k) := by
      rw [show tubeCenters i l k - tubeCurve i l u =
        (-1 : ℝ) • (tubeCurve i l u - tubeCenters i l k) by module,
        TimeChange.euclideanNorm_smul]
      norm_num
    rw [sub_add_sub_cancel, hneg] at htriangle
    exact htriangle
  change euclideanNorm (lam • Y s - tubeCurve i l u) < l / 32
  change euclideanNorm (tubeCurve i l u - tubeCenters i l k) ≤ (l / 32) / 16 at hcurve
  linarith only [hnorm, hblock, hcurve, hl]

/-- A two-valued Sobolev function on a connected convex domain is constant
almost everywhere. Level-set gradient vanishing and Poincaré supply the proof. -/
theorem h1_twoValue_rigidity {d : ℕ} {U : Set (Vec d)}
    (hU : PDE.IsOpenBoundedConvexDomain U)
    (hUpos : 0 < volume U) (hUfin : volume U < ∞) (u : PDE.H1Function U)
    (hvalues : ∀ᵐ x ∂PDE.volumeOn U, u.toFun x = 0 ∨ u.toFun x = 1) :
    (u.toFun =ᵐ[PDE.volumeOn U] fun _ => 0) ∨
      (u.toFun =ᵐ[PDE.volumeOn U] fun _ => 1) := by
  have hgrad : u.grad =ᵐ[PDE.volumeOn U] 0 := by
    filter_upwards [hvalues, u.grad_ae_zero_on_level_set hU 0,
      u.grad_ae_zero_on_level_set hU 1] with x hx hzero hone
    exact hx.elim hzero hone
  have hconst := PDE.W1pFunction.ae_eq_integralAverage_of_grad_ae_eq_zero
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    hU hUpos hUfin u.toW1pFunction hgrad
  by_cases hc : PDE.integralAverage U u.toFun = 0
  · exact Or.inl (by simpa only [PDE.H1Function.toW1pFunction_toFun, hc] using hconst)
  · right
    filter_upwards [hvalues, hconst] with x hx hcx
    rcases hx with hx | hx
    · exact (hc (hcx.symm.trans hx)).elim
    · exact hx

/-- On a compact region a continuous positive weight controls the literal
Lebesgue L² norm, for scalar or Euclidean-valued representatives. -/
theorem memLp_restrict_volume_of_posDensity {d : ℕ} {E : Type*}
    [NormedAddCommGroup E]
    (ρ : Vec d → ℝ) (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    {U K : Set (Vec d)} (hU : MeasurableSet U) (hK : IsCompact K)
    (hKne : K.Nonempty) (hUK : U ⊆ K) {f : Vec d → E}
    (hf : MemLp f 2 (volume.withDensity (fun x => ENNReal.ofReal (ρ x)))) :
    MemLp f 2 (volume.restrict U) := by
  obtain ⟨z, hz, hmin⟩ := hK.exists_isMinOn hKne hρ.continuousOn
  have hmin' : ∀ y ∈ K, ρ z ≤ ρ y := by
    simpa [IsMinOn, IsMinFilter] using hmin
  let c : ℝ≥0∞ := ENNReal.ofReal (ρ z)
  have hc0 : c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (hρpos z))
  have hcfin : c ≠ ∞ := ENNReal.ofReal_ne_top
  have hle : c • volume.restrict U ≤
      (volume.withDensity (fun x => ENNReal.ofReal (ρ x))).restrict U := by
    rw [restrict_withDensity hU, ← withDensity_const]
    apply withDensity_mono
    filter_upwards [ae_restrict_mem hU] with x hx
    exact ENNReal.ofReal_le_ofReal (hmin' x (hUK hx))
  have hinv := smul_le_smul_left c⁻¹ hle
  rw [smul_smul, ENNReal.inv_mul_cancel hc0 hcfin, one_smul] at hinv
  exact (hf.restrict U).of_measure_le_smul (ENNReal.inv_ne_top.mpr hc0) hinv

/-- Restrict the actual weighted weak-gradient graph to an ordinary bounded
Sobolev domain. Both representatives and the distributional identity are preserved. -/
def weightedSobolevGraphH1Restrict {d : ℕ}
    (ρ : Vec d → ℝ) (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    {U K : Set (Vec d)} (hU : MeasurableSet U) (hK : IsCompact K)
    (hKne : K.Nonempty) (hUK : U ⊆ K)
    (u : SpatialDirichlet.WeightedSobolevGraph
      (volume.withDensity (fun x => ENNReal.ofReal (ρ x)))) : PDE.H1Function U where
  toFun := u.value
  grad := fun x => WithLp.ofLp (u.weakGradient x)
  memL2 := memLp_restrict_volume_of_posDensity ρ hρ hρpos hU hK hKne hUK u.value_memLp
  gradMemL2 := by
    intro i
    have hg := memLp_restrict_volume_of_posDensity ρ hρ hρpos hU hK hKne hUK
      u.gradient_memLp
    exact hg.of_le ((PiLp.continuous_apply 2 _ i).comp_aestronglyMeasurable
      hg.aestronglyMeasurable) (Eventually.of_forall fun x => PiLp.norm_apply_le (u.weakGradient x) i)
  hasWeakGradient := by
    intro i φ hφ hc hs
    have hloc := Correctors.hasWeakGradient_mono (Set.subset_univ U) u.distributionalGradient
    exact (hloc i).2.2 φ ⟨hφ, hc, hs⟩

/-- A representative of the actual weighted weak-gradient graph cannot take
only the values zero and one nontrivially on a bounded convex domain. -/
theorem weightedSobolevGraph_twoValue_rigidity {d : ℕ}
    (ρ : Vec d → ℝ) (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    {U : Set (Vec d)} (hU : PDE.IsOpenBoundedConvexDomain U)
    (hUpos : 0 < volume U) (hUfin : volume U < ∞)
    (u : SpatialDirichlet.WeightedSobolevGraph
      (volume.withDensity (fun x => ENNReal.ofReal (ρ x))))
    (hvalues : ∀ᵐ x ∂volume.restrict U, u.value x = 0 ∨ u.value x = 1) :
    (u.value =ᵐ[volume.restrict U] fun _ => 0) ∨
      (u.value =ᵐ[volume.restrict U] fun _ => 1) := by
  obtain ⟨R, hR, hb⟩ := hU.isBoundedDomain
  let K : Set (Vec d) := Set.Icc (fun _ => -R) (fun _ => R)
  have hK : IsCompact K := isCompact_Icc
  have hKne : K.Nonempty := ⟨0, by
    constructor
    · intro i
      change -R ≤ (0 : ℝ)
      linarith
    · intro i
      change (0 : ℝ) ≤ R
      exact hR.le⟩
  have hUK : U ⊆ K := by
    intro x hx
    constructor <;> intro i
    · exact (abs_le.mp (hb x hx i)).1
    · exact (abs_le.mp (hb x hx i)).2
  exact h1_twoValue_rigidity hU hUpos hUfin
    (weightedSobolevGraphH1Restrict ρ hρ hρpos hU.measurableSet hK hKne hUK u) hvalues

section GMPBounds

variable {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L} {ω : FieldPair d}
  {hω : IsRegular L ω} {lam : ℝ} {h₀ : 0 ≤ lam} {h₁ : lam ≤ 1}
  (G : GantertFixedEnvironmentRealization hd L hL ω hω lam h₀ h₁)

/-- A discrete positive-time bound for the actual killed correlation decrement. -/
theorem killedL2_correlation_increment_at_n_le
    (U : Set (Vec d)) (hU : IsOpen U) (h : ℝ≥0)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : f ∈ physicalZeroBoundaryL2 U hd ω lam L hω) (n : ℕ) :
    (n : ℝ) * (⟪gmpKilledL2Operator G U hU (n • h) f, f⟫_ℝ -
      ⟪gmpKilledL2Operator G U hU ((n + 1) • h) f, f⟫_ℝ) ≤ ‖f‖ ^ 2 := by
  let q : ℕ → ℝ := fun k => ⟪gmpKilledL2Operator G U hU (k • h) f, f⟫_ℝ
  have hstep (k : ℕ) : q (k + 1) - q (k + 2) ≤ q k - q (k + 1) := by
    have hx := gmpKilledL2_correlation_second_difference_nonneg G U hU (k • h) h f
    dsimp only [q]
    simp only [add_nsmul, one_nsmul, two_nsmul]
    linarith
  have hmono : Antitone (fun k => q k - q (k + 1)) :=
    antitone_nat_of_succ_le hstep
  have htel (m : ℕ) (hmn : m ≤ n) : (m : ℝ) * (q n - q (n + 1)) ≤ q 0 - q m := by
    induction m with
    | zero => simp
    | succ m ih =>
      have hs := hmono (Nat.le_of_lt (Nat.lt_of_succ_le hmn))
      have hi := ih (Nat.le_trans (Nat.le_succ m) hmn)
      push_cast
      linarith
  have hq0 : q 0 = ‖f‖ ^ 2 := by
    dsimp only [q]
    rw [zero_nsmul]
    rw [show gmpKilledL2Operator G U hU 0 f = f from
      congrArg Subtype.val (gmpKilledInteriorOperator_zero G U hU ⟨f, hf⟩)]
    exact real_inner_self_eq_norm_sq f
  have hqn : 0 ≤ q n := gmpKilledL2_inner_nonneg G U hU (n • h) f
  have ht := htel n le_rfl
  rw [hq0] at ht
  dsimp only [q] at ht ⊢
  linarith

/-- Every positive-time killed correlation decrement is nonnegative. -/
theorem killedL2_correlation_increment_nonneg
    (U : Set (Vec d)) (hU : IsOpen U) (t h : ℝ≥0)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    0 ≤ ⟪gmpKilledL2Operator G U hU t f, f⟫_ℝ -
      ⟪gmpKilledL2Operator G U hU (t + h) f, f⟫_ℝ := by
  let T := gmpKilledL2Operator G U hU
  let a : ℝ≥0 := t / 2
  have ha : a + a = t := by dsimp [a]; exact add_halves t
  have hq := gmpKilledL2_inner_sub_nonneg G U hU h (T a f)
  have he₁ : ⟪T t f, f⟫_ℝ = ⟪T a f, T a f⟫_ℝ := by
    dsimp only [T]
    rw [← ha, gmpKilledL2Operator_add_time, ContinuousLinearMap.comp_apply]
    exact gmpKilledL2Operator_isSymmetric G U hU a (T a f) f
  have he₂ : ⟪T (t + h) f, f⟫_ℝ = ⟪T h (T a f), T a f⟫_ℝ := by
    dsimp only [T]
    rw [← ha, gmpKilledL2Operator_add_time, ContinuousLinearMap.comp_apply,
      gmpKilledL2Operator_add_time, ContinuousLinearMap.comp_apply]
    have hc : T a (T a (T h f)) = T a (T h (T a f)) := by
      apply congrArg (T a)
      dsimp only [T]
      rw [← ContinuousLinearMap.comp_apply, ← gmpKilledL2Operator_add_time,
        ← ContinuousLinearMap.comp_apply, ← gmpKilledL2Operator_add_time, add_comm a h]
    rw [hc]
    exact gmpKilledL2Operator_isSymmetric G U hU a (T h (T a f)) f
  change 0 ≤ ⟪T t f, f⟫_ℝ - ⟪T (t + h) f, f⟫_ℝ
  rw [he₁, he₂]
  simpa only [inner_sub_left] using hq

/-- Polarization bounds mixed killed correlation decrements by the two input norms. -/
theorem killedL2_correlation_increment_polarized_le
    (U : Set (Vec d)) (hU : IsOpen U) (h : ℝ≥0)
    (f g : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : f ∈ physicalZeroBoundaryL2 U hd ω lam L hω)
    (hg : g ∈ physicalZeroBoundaryL2 U hd ω lam L hω) (n : ℕ) :
    (n : ℝ) * |⟪gmpKilledL2Operator G U hU (n • h) f -
      gmpKilledL2Operator G U hU ((n + 1) • h) f, g⟫_ℝ| ≤
      (‖f‖ ^ 2 + ‖g‖ ^ 2) / 2 := by
  let T := gmpKilledL2Operator G U hU
  let t : ℝ≥0 := n • h
  let u : ℝ≥0 := (n + 1) • h
  have hu : u = t + h := by
    dsimp only [u, t]
    rw [add_nsmul, one_nsmul]
  have hp := killedL2_correlation_increment_at_n_le G U hU h (f + g)
    ((physicalZeroBoundaryL2 U hd ω lam L hω).add_mem hf hg) n
  have hm := killedL2_correlation_increment_at_n_le G U hU h (f - g)
    ((physicalZeroBoundaryL2 U hd ω lam L hω).sub_mem hf hg) n
  have hpp := killedL2_correlation_increment_nonneg G U hU t h (f + g)
  have hmm := killedL2_correlation_increment_nonneg G U hU t h (f - g)
  change (n : ℝ) * (⟪T t (f + g), f + g⟫_ℝ - ⟪T u (f + g), f + g⟫_ℝ) ≤ _ at hp
  change (n : ℝ) * (⟪T t (f - g), f - g⟫_ℝ - ⟪T u (f - g), f - g⟫_ℝ) ≤ _ at hm
  change 0 ≤ ⟪T t (f + g), f + g⟫_ℝ - ⟪T (t + h) (f + g), f + g⟫_ℝ at hpp
  change 0 ≤ ⟪T t (f - g), f - g⟫_ℝ - ⟪T (t + h) (f - g), f - g⟫_ℝ at hmm
  rw [← hu] at hpp hmm
  have ht := gmpKilledL2Operator_isSymmetric G U hU t f g
  have ht' := gmpKilledL2Operator_isSymmetric G U hU u f g
  change ⟪T t f, g⟫_ℝ = ⟪f, T t g⟫_ℝ at ht
  change ⟪T u f, g⟫_ℝ = ⟪f, T u g⟫_ℝ at ht'
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hpp' := mul_nonneg hn hpp
  have hmm' := mul_nonneg hn hmm
  simp only [map_add, map_sub, inner_add_left, inner_sub_left,
    inner_add_right, inner_sub_right] at hp hm hpp' hmm'
  rw [norm_add_sq_real] at hp
  rw [norm_sub_sq_real] at hm
  have hs : ⟪T t g, f⟫_ℝ = ⟪T t f, g⟫_ℝ := by
    rw [real_inner_comm, ← ht]
  have hs' : ⟪T u g, f⟫_ℝ = ⟪T u f, g⟫_ℝ := by
    rw [real_inner_comm, ← ht']
  rw [hs, hs'] at hp hm hpp' hmm'
  change (n : ℝ) * |⟪T t f - T u f, g⟫_ℝ| ≤ _
  rw [← abs_of_nonneg hn, ← abs_mul]
  apply abs_le.mpr
  rw [inner_sub_left]
  constructor <;> nlinarith

/-- The killed evolution has a linear equal-step L² increment bound. -/
theorem killedL2_linear_increment_at_n_le
    (U : Set (Vec d)) (hU : IsOpen U) (h : ℝ≥0)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : f ∈ physicalZeroBoundaryL2 U hd ω lam L hω) (n : ℕ) :
    (n : ℝ) * ‖gmpKilledL2Operator G U hU (n • h) f -
      gmpKilledL2Operator G U hU ((n + 1) • h) f‖ ≤ ‖f‖ := by
  let D := gmpKilledL2Operator G U hU (n • h) f -
    gmpKilledL2Operator G U hU ((n + 1) • h) f
  change (n : ℝ) * ‖D‖ ≤ ‖f‖
  have hDmem : D ∈ physicalZeroBoundaryL2 U hd ω lam L hω :=
    (physicalZeroBoundaryL2 U hd ω lam L hω).sub_mem
      (gmpKilledL2_mem_zeroBoundaryL2 G U hU (n • h) f)
      (gmpKilledL2_mem_zeroBoundaryL2 G U hU ((n + 1) • h) f)
  by_cases hf0 : f = 0
  · subst f
    simp [D]
  by_cases hD0 : D = 0
  · simp [hD0]
  have hfpos : 0 < ‖f‖ := norm_pos_iff.mpr hf0
  have hDpos : 0 < ‖D‖ := norm_pos_iff.mpr hD0
  let c : ℝ := ‖f‖ / ‖D‖
  have hc : 0 ≤ c := div_nonneg (norm_nonneg _) (norm_nonneg _)
  have hcD : c * ‖D‖ = ‖f‖ := div_mul_cancel₀ _ (ne_of_gt hDpos)
  have hh := killedL2_correlation_increment_polarized_le G U hU h f (c • D) hf
    ((physicalZeroBoundaryL2 U hd ω lam L hω).smul_mem c hDmem) n
  change (n : ℝ) * |⟪D, c • D⟫_ℝ| ≤ (‖f‖ ^ 2 + ‖c • D‖ ^ 2) / 2 at hh
  have hnorm : ‖c • D‖ = ‖f‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, hcD]
  have hinner : |⟪D, c • D⟫_ℝ| = c * ‖D‖ ^ 2 := by
    rw [inner_smul_right, real_inner_self_eq_norm_sq, abs_mul,
      abs_of_nonneg hc, abs_of_nonneg (sq_nonneg _)]
  have hfactor : c * ‖D‖ ^ 2 = ‖f‖ * ‖D‖ := by
    rw [pow_two, ← mul_assoc, hcD]
  rw [hinner, hfactor, hnorm] at hh
  have hcancel : ‖f‖ * ((n : ℝ) * ‖D‖) ≤ ‖f‖ * ‖f‖ := by nlinarith [hh]
  exact le_of_mul_le_mul_left hcancel hfpos

/-- A nonnegative time remainder preserves the linear mesh-step bound. -/
theorem killedL2_linear_increment_after_mesh_le
    (U : Set (Vec d)) (hU : IsOpen U) (h r : ℝ≥0)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) (n : ℕ) :
    (n : ℝ) * ‖gmpKilledL2Operator G U hU (n • h + r) f -
      gmpKilledL2Operator G U hU (n • h + r + h) f‖ ≤ ‖f‖ := by
  let g := gmpKilledL2Operator G U hU r f
  have hg : g ∈ physicalZeroBoundaryL2 U hd ω lam L hω :=
    gmpKilledL2_mem_zeroBoundaryL2 G U hU r f
  have hstep := killedL2_linear_increment_at_n_le G U hU h g hg n
  have ht : n • h + r + h = (n + 1) • h + r := by
    simp only [add_nsmul, one_nsmul]
    ac_rfl
  rw [ht, gmpKilledL2Operator_add_time, gmpKilledL2Operator_add_time,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  have hnorm : ‖g‖ ≤ ‖f‖ := by
    simpa only [g, gmpKilledL2Operator_apply] using (gmpKilledL2_norm_le G U hU r f)
  exact hstep.trans hnorm

/-- A mesh lower bound gives a linear increment estimate at any later time. -/
theorem killedL2_linear_increment_at_time_le
    (U : Set (Vec d)) (hU : IsOpen U) (t h : ℝ≥0)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) (n : ℕ)
    (hn : n • h ≤ t) :
    (n : ℝ) * ‖gmpKilledL2Operator G U hU t f -
      gmpKilledL2Operator G U hU (t + h) f‖ ≤ ‖f‖ := by
  have ht : n • h + (t - n • h) = t := by
    simpa only [add_comm] using tsub_add_cancel_of_le hn
  simpa only [ht] using
    killedL2_linear_increment_after_mesh_le G U hU h (t - n • h) f n

/-- At positive time the actual killed semigroup has linear time increments. -/
theorem killedL2_linear_increment_positive_time_le
    (U : Set (Vec d)) (hU : IsOpen U) (t h : ℝ≥0)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hh : 0 < h) (ht : h ≤ t) :
    (t : ℝ) * ‖gmpKilledL2Operator G U hU t f -
      gmpKilledL2Operator G U hU (t + h) f‖ ≤ 2 * (h : ℝ) * ‖f‖ := by
  have hhpos : 0 < (h : ℝ) := by exact_mod_cast hh
  have htle : (h : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  let x : ℝ := (t : ℝ) / (h : ℝ)
  let n : ℕ := ⌊x⌋₊
  have hx : 1 ≤ x := (one_le_div hhpos).2 htle
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (Nat.one_le_floor_iff x).2 hx
  have hfloor : (n : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hfloor' : x < (n : ℝ) + 1 := Nat.lt_floor_add_one x
  have hxbound : x ≤ 2 * (n : ℝ) := by linarith
  have hnmeshreal : (n : ℝ) * (h : ℝ) ≤ (t : ℝ) := by
    exact (le_div_iff₀ hhpos).mp hfloor
  have hnmesh : n • h ≤ t := by
    apply NNReal.coe_le_coe.mp
    simpa only [nsmul_eq_mul, NNReal.coe_mul, NNReal.coe_natCast] using hnmeshreal
  have htbound : (t : ℝ) ≤ 2 * (n : ℝ) * (h : ℝ) := by
    exact (div_le_iff₀ hhpos).mp hxbound
  have hstep := killedL2_linear_increment_at_time_le G U hU t h f n hnmesh
  have hnorm := norm_nonneg (gmpKilledL2Operator G U hU t f -
    gmpKilledL2Operator G U hU (t + h) f)
  calc
    (t : ℝ) * ‖gmpKilledL2Operator G U hU t f -
        gmpKilledL2Operator G U hU (t + h) f‖ ≤
      (2 * (n : ℝ) * (h : ℝ)) * ‖gmpKilledL2Operator G U hU t f -
        gmpKilledL2Operator G U hU (t + h) f‖ := mul_le_mul_of_nonneg_right htbound hnorm
    _ = (2 * (h : ℝ)) * ((n : ℝ) * ‖gmpKilledL2Operator G U hU t f -
        gmpKilledL2Operator G U hU (t + h) f‖) := by ring
    _ ≤ 2 * (h : ℝ) * ‖f‖ :=
      mul_le_mul_of_nonneg_left hstep (by positivity)

/-- The linear time-increment estimate also holds for zero and large steps. -/
theorem killedL2_linear_increment_all_steps_le
    (U : Set (Vec d)) (hU : IsOpen U) (t h : ℝ≥0)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    (t : ℝ) * ‖gmpKilledL2Operator G U hU t f -
      gmpKilledL2Operator G U hU (t + h) f‖ ≤ 2 * (h : ℝ) * ‖f‖ := by
  by_cases hh : h = 0
  · subst h
    simp
  by_cases ht : h ≤ t
  · exact killedL2_linear_increment_positive_time_le G U hU t h f
      (pos_iff_ne_zero.mpr hh) ht
  · have hlarge : (t : ℝ) ≤ (h : ℝ) := by exact_mod_cast (le_of_lt (lt_of_not_ge ht))
    have hfirst : ‖gmpKilledL2Operator G U hU t f‖ ≤ ‖f‖ := by
      simpa only [gmpKilledL2Operator_apply] using (gmpKilledL2_norm_le G U hU t f)
    have hsecond : ‖gmpKilledL2Operator G U hU (t + h) f‖ ≤ ‖f‖ := by
      simpa only [gmpKilledL2Operator_apply] using (gmpKilledL2_norm_le G U hU (t + h) f)
    have hdiff : ‖gmpKilledL2Operator G U hU t f -
        gmpKilledL2Operator G U hU (t + h) f‖ ≤ 2 * ‖f‖ := by
      calc
        _ ≤ ‖gmpKilledL2Operator G U hU t f‖ +
            ‖gmpKilledL2Operator G U hU (t + h) f‖ := norm_sub_le _ _
        _ ≤ 2 * ‖f‖ := by linarith
    calc
      (t : ℝ) * ‖gmpKilledL2Operator G U hU t f -
          gmpKilledL2Operator G U hU (t + h) f‖ ≤ (t : ℝ) * (2 * ‖f‖) :=
        mul_le_mul_of_nonneg_left hdiff (NNReal.coe_nonneg t)
      _ ≤ (h : ℝ) * (2 * ‖f‖) :=
        mul_le_mul_of_nonneg_right hlarge (by positivity)
      _ = 2 * (h : ℝ) * ‖f‖ := by ring

/-- Repeated positive-time increments retain the linear bound at every step. -/
theorem killedL2_iterated_linear_increment_positive_time_le
    (U : Set (Vec d)) (hU : IsOpen U) (t h : ℝ≥0)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hh : 0 < h) (ht : h ≤ t) (k : ℕ) :
    let T := gmpKilledL2Operator G U hU
    let D := fun g => T t g - T (t + h) g
    (t : ℝ) ^ k * ‖D^[k] f‖ ≤ (2 * (h : ℝ)) ^ k * ‖f‖ := by
  dsimp only
  let D := fun g => gmpKilledL2Operator G U hU t g -
    gmpKilledL2Operator G U hU (t + h) g
  change (t : ℝ) ^ k * ‖D^[k] f‖ ≤ (2 * (h : ℝ)) ^ k * ‖f‖
  induction k generalizing f with
  | zero => simp only [pow_zero, Function.iterate_zero, id_eq, one_mul, le_refl]
  | succ k ih =>
    have hk := ih (D f)
    have hstep : (t : ℝ) * ‖D f‖ ≤ 2 * (h : ℝ) * ‖f‖ :=
      killedL2_linear_increment_positive_time_le G U hU t h f hh ht
    rw [Function.iterate_succ_apply, pow_succ, pow_succ]
    calc
      (t : ℝ) ^ k * (t : ℝ) * ‖D^[k] (D f)‖ =
          (t : ℝ) * ((t : ℝ) ^ k * ‖D^[k] (D f)‖) := by ring
      _ ≤ (t : ℝ) * ((2 * (h : ℝ)) ^ k * ‖D f‖) :=
        mul_le_mul_of_nonneg_left hk (NNReal.coe_nonneg t)
      _ = (2 * (h : ℝ)) ^ k * ((t : ℝ) * ‖D f‖) := by ring
      _ ≤ (2 * (h : ℝ)) ^ k * (2 * (h : ℝ) * ‖f‖) :=
        mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = (2 * (h : ℝ)) ^ k * (2 * (h : ℝ)) * ‖f‖ := by ring

/-- Repeated increments retain the linear bound for all step sizes. -/
theorem killedL2_iterated_linear_increment_all_steps_le
    (U : Set (Vec d)) (hU : IsOpen U) (t h : ℝ≥0)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (k : ℕ) :
    let T := gmpKilledL2Operator G U hU
    let D := fun g => T t g - T (t + h) g
    (t : ℝ) ^ k * ‖D^[k] f‖ ≤ (2 * (h : ℝ)) ^ k * ‖f‖ := by
  dsimp only
  let D := fun g => gmpKilledL2Operator G U hU t g -
    gmpKilledL2Operator G U hU (t + h) g
  change (t : ℝ) ^ k * ‖D^[k] f‖ ≤ (2 * (h : ℝ)) ^ k * ‖f‖
  induction k generalizing f with
  | zero => simp only [pow_zero, Function.iterate_zero, id_eq, one_mul, le_refl]
  | succ k ih =>
    have hk := ih (D f)
    have hstep : (t : ℝ) * ‖D f‖ ≤ 2 * (h : ℝ) * ‖f‖ :=
      killedL2_linear_increment_all_steps_le G U hU t h f
    rw [Function.iterate_succ_apply, pow_succ, pow_succ]
    calc
      (t : ℝ) ^ k * (t : ℝ) * ‖D^[k] (D f)‖ =
          (t : ℝ) * ((t : ℝ) ^ k * ‖D^[k] (D f)‖) := by ring
      _ ≤ (t : ℝ) * ((2 * (h : ℝ)) ^ k * ‖D f‖) :=
        mul_le_mul_of_nonneg_left hk (NNReal.coe_nonneg t)
      _ = (2 * (h : ℝ)) ^ k * ((t : ℝ) * ‖D f‖) := by ring
      _ ≤ (2 * (h : ℝ)) ^ k * (2 * (h : ℝ) * ‖f‖) :=
        mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = (2 * (h : ℝ)) ^ k * (2 * (h : ℝ)) * ‖f‖ := by ring

/-- The second increment at time `s + s` is the square of the increment at `s`. -/
theorem killedL2_second_increment_eq_iterate
    (U : Set (Vec d)) (hU : IsOpen U) (s h : ℝ≥0)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    let T := gmpKilledL2Operator G U hU
    let D := fun g => T s g - T (s + h) g
    (T (s + s) f - T (s + s + h) f) -
      (T (s + s + h) f - T (s + s + (h + h)) f) = D^[2] f := by
  dsimp only
  let T := gmpKilledL2Operator G U hU
  let D := fun g => T s g - T (s + h) g
  change (T (s + s) f - T (s + s + h) f) -
      (T (s + s + h) f - T (s + s + (h + h)) f) = D^[2] f
  have hcomp (u v : ℝ≥0) : T u (T v f) = T (u + v) f := by
    dsimp only [T]
    rw [gmpKilledL2Operator_add_time, ContinuousLinearMap.comp_apply]
  have h₁ : s + (s + h) = s + s + h := by ac_rfl
  have h₂ : (s + h) + s = s + s + h := by ac_rfl
  have h₃ : (s + h) + (s + h) = s + s + (h + h) := by ac_rfl
  simp only [Function.iterate_succ_apply, Function.iterate_zero, id_eq, D,
    map_sub, hcomp, h₁, h₂, h₃]

/-- Successive increment differences satisfy a quadratic step bound. -/
theorem killedL2_second_increment_bound
    (U : Set (Vec d)) (hU : IsOpen U) (s h : ℝ≥0)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    let T := gmpKilledL2Operator G U hU
    (s : ℝ) ^ 2 * ‖(T (s + s) f - T (s + s + h) f) -
      (T (s + s + h) f - T (s + s + (h + h)) f)‖ ≤
      (2 * (h : ℝ)) ^ 2 * ‖f‖ := by
  dsimp only
  rw [killedL2_second_increment_eq_iterate G U hU s h f]
  exact killedL2_iterated_linear_increment_all_steps_le G U hU s h f 2

/-- Adjacent normalized time increments differ by at most a linear step error. -/
theorem killedL2_adjacent_difference_quotients_bound
    (U : Set (Vec d)) (hU : IsOpen U) (s h : ℝ≥0)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) (hh : 0 < h) :
    let T := gmpKilledL2Operator G U hU
    (s : ℝ) ^ 2 * ‖(h : ℝ)⁻¹ • ((T (s + s) f - T (s + s + h) f) -
      (T (s + s + h) f - T (s + s + (h + h)) f))‖ ≤
      4 * (h : ℝ) * ‖f‖ := by
  dsimp only
  have hhreal : 0 < (h : ℝ) := by exact_mod_cast hh
  have hbound := killedL2_second_increment_bound G U hU s h f
  dsimp only at hbound
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hhreal.le)]
  calc
    (s : ℝ) ^ 2 * ((h : ℝ)⁻¹ * ‖(gmpKilledL2Operator G U hU (s + s) f -
        gmpKilledL2Operator G U hU (s + s + h) f) -
        (gmpKilledL2Operator G U hU (s + s + h) f -
        gmpKilledL2Operator G U hU (s + s + (h + h)) f)‖) =
      (h : ℝ)⁻¹ * ((s : ℝ) ^ 2 * ‖(gmpKilledL2Operator G U hU (s + s) f -
        gmpKilledL2Operator G U hU (s + s + h) f) -
        (gmpKilledL2Operator G U hU (s + s + h) f -
        gmpKilledL2Operator G U hU (s + s + (h + h)) f)‖) := by ring
    _ ≤ (h : ℝ)⁻¹ * ((2 * (h : ℝ)) ^ 2 * ‖f‖) :=
      mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hhreal.le)
    _ = 4 * (h : ℝ) * ‖f‖ := by field_simp; ring

/-- Dyadic difference quotients at a positive time converge strongly in the killed L² space. -/
theorem killedL2_dyadic_difference_quotients_converge
    (U : Set (Vec d)) (hU : IsOpen U) (s : ℝ≥0) (hs : 0 < s)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    let T := gmpKilledL2Operator G U hU
    let h : ℕ → ℝ≥0 := fun n => (1 / 2 : ℝ≥0) ^ n
    ∃ g, Tendsto (fun n => ((h n : ℝ)⁻¹) •
      (T (s + s) f - T (s + s + h n) f)) atTop (nhds g) := by
  dsimp only
  let T := gmpKilledL2Operator G U hU
  let h : ℕ → ℝ≥0 := fun n => (1 / 2 : ℝ≥0) ^ n
  let q := fun n => ((h n : ℝ)⁻¹) • (T (s + s) f - T (s + s + h n) f)
  change ∃ g, Tendsto q atTop (nhds g)
  have hsreal : 0 < (s : ℝ) := by exact_mod_cast hs
  have hh (n : ℕ) : 0 < h n := by dsimp [h]; positivity
  have hdouble (n : ℕ) : h (n + 1) + h (n + 1) = h n := by
    dsimp [h]
    rw [pow_succ]
    ring
  have hreal (n : ℕ) : (h n : ℝ) = (1 / 2 : ℝ) ^ n := by simp [h]
  have hq (n : ℕ) :
      q (n + 1) - q n = (1 / 2 : ℝ) • ((h (n + 1) : ℝ)⁻¹ •
        ((T (s + s) f - T (s + s + h (n + 1)) f) -
        (T (s + s + h (n + 1)) f - T (s + s + (h (n + 1) + h (n + 1))) f))) := by
    have hd : (h n : ℝ) = (h (n + 1) : ℝ) + (h (n + 1) : ℝ) := by
      exact_mod_cast (hdouble n).symm
    have hi : (h n : ℝ)⁻¹ = (1 / 2 : ℝ) * (h (n + 1) : ℝ)⁻¹ := by
      rw [hd, ← two_mul, mul_inv_rev]
      norm_num
      ring
    have hmiddle :
        (T (s + s) f - T (s + s + h (n + 1)) f) -
            (1 / 2 : ℝ) • (T (s + s) f - T (s + s + (h (n + 1) + h (n + 1))) f) =
          (1 / 2 : ℝ) • ((T (s + s) f - T (s + s + h (n + 1)) f) -
            (T (s + s + h (n + 1)) f - T (s + s + (h (n + 1) + h (n + 1))) f)) := by
      have hA : (1 / 2 : ℝ) • T (s + s) f + (1 / 2 : ℝ) • T (s + s) f = T (s + s) f := by
        rw [← add_smul]
        norm_num
      have hB : (1 / 2 : ℝ) • T (s + s + h (n + 1)) f +
          (1 / 2 : ℝ) • T (s + s + h (n + 1)) f = T (s + s + h (n + 1)) f := by
        rw [← add_smul]
        norm_num
      nth_rewrite 1 [← hA]
      nth_rewrite 1 [← hB]
      simp only [smul_sub]
      abel
    dsimp only [q]
    rw [hi, mul_smul, ← hdouble n, smul_comm (1 / 2 : ℝ), ← smul_sub, hmiddle,
      smul_comm (h (n + 1) : ℝ)⁻¹]
  have hc : CauchySeq q := by
    apply SeminormedAddCommGroup.cauchySeq_of_le_geometric (C := 2 * ‖f‖ / (s : ℝ) ^ 2)
      (r := (1 / 2 : ℝ)) (by norm_num)
    intro n
    have hb := killedL2_adjacent_difference_quotients_bound G U hU s (h (n + 1)) f (hh (n + 1))
    dsimp only at hb
    have hsq : 0 < (s : ℝ) ^ 2 := sq_pos_of_pos hsreal
    rw [norm_sub_rev, hq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    conv_rhs => rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hsq).2
    rw [hreal]
    rw [hreal, pow_succ] at hb
    dsimp only [T]
    simp only [pow_succ, pow_one] at hb ⊢
    have hprod : 0 ≤ (1 / 2 : ℝ) ^ n * ‖f‖ := mul_nonneg (by positivity) (norm_nonneg f)
    nlinarith [hb, hprod]
  exact cauchySeq_tendsto_of_complete hc

/-- The strong dyadic derivative limit satisfies the positive-time first-order bound. -/
theorem killedL2_dyadic_difference_quotients_converge_bound
    (U : Set (Vec d)) (hU : IsOpen U) (s : ℝ≥0) (hs : 0 < s)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    let T := gmpKilledL2Operator G U hU
    let h : ℕ → ℝ≥0 := fun n => (1 / 2 : ℝ≥0) ^ n
    ∃ g, Tendsto (fun n => ((h n : ℝ)⁻¹) •
      (T (s + s) f - T (s + s + h n) f)) atTop (nhds g) ∧
      (s : ℝ) * ‖g‖ ≤ ‖f‖ := by
  dsimp only
  obtain ⟨g, hg⟩ := killedL2_dyadic_difference_quotients_converge G U hU s hs f
  refine ⟨g, hg, ?_⟩
  apply le_of_tendsto (tendsto_const_nhds.mul hg.norm)
  filter_upwards with n
  let h : ℝ≥0 := (1 / 2 : ℝ≥0) ^ n
  have hh : 0 < (h : ℝ) := by dsimp [h]; positivity
  have hb := killedL2_linear_increment_all_steps_le G U hU (s + s) h f
  change (s : ℝ) * ‖(h : ℝ)⁻¹ • (gmpKilledL2Operator G U hU (s + s) f -
    gmpKilledL2Operator G U hU (s + s + h) f)‖ ≤ ‖f‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hh)]
  calc
    (s : ℝ) * ((h : ℝ)⁻¹ * ‖gmpKilledL2Operator G U hU (s + s) f -
        gmpKilledL2Operator G U hU (s + s + h) f‖) =
      ((1 / 2 : ℝ) * (h : ℝ)⁻¹) * ((s + s : ℝ≥0) : ℝ) *
        ‖gmpKilledL2Operator G U hU (s + s) f -
        gmpKilledL2Operator G U hU (s + s + h) f‖ := by push_cast; ring
    _ ≤ ((1 / 2 : ℝ) * (h : ℝ)⁻¹) * (2 * (h : ℝ) * ‖f‖) := by
      simpa only [mul_assoc] using
        (mul_le_mul_of_nonneg_left hb (show 0 ≤ (1 / 2 : ℝ) * (h : ℝ)⁻¹ by positivity))
    _ = ‖f‖ := by field_simp

/-- Iterated dyadic quotients converge strongly at positive time. -/
theorem killedL2_iterated_dyadic_quotients_converge
    (U : Set (Vec d)) (hU : IsOpen U) (s : ℝ≥0) (hs : 0 < s)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) (k : ℕ) :
    let T := gmpKilledL2Operator G U hU
    let h : ℕ → ℝ≥0 := fun n => (1 / 2 : ℝ≥0) ^ n
    let q := fun n x => ((h n : ℝ)⁻¹) • (T (s + s) x - T (s + s + h n) x)
    ∃ g, Tendsto (fun n => (q n)^[k] f) atTop (nhds g) := by
  dsimp only
  let T := gmpKilledL2Operator G U hU
  let h : ℕ → ℝ≥0 := fun n => (1 / 2 : ℝ≥0) ^ n
  let q := fun n x => ((h n : ℝ)⁻¹) • (T (s + s) x - T (s + s + h n) x)
  change ∃ g, Tendsto (fun n => (q n)^[k] f) atTop (nhds g)
  have hsreal : 0 < (s : ℝ) := by exact_mod_cast hs
  have hbound (n : ℕ) (x : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
      ‖q n x‖ ≤ (s : ℝ)⁻¹ * ‖x‖ := by
    have hh : 0 < (h n : ℝ) := by dsimp [h]; positivity
    have hb := killedL2_linear_increment_all_steps_le G U hU (s + s) (h n) x
    have hsbound : (s : ℝ) * ‖q n x‖ ≤ ‖x‖ := by
      dsimp only [q, T]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hh)]
      calc
        (s : ℝ) * ((h n : ℝ)⁻¹ * ‖gmpKilledL2Operator G U hU (s + s) x -
            gmpKilledL2Operator G U hU (s + s + h n) x‖) =
          ((1 / 2 : ℝ) * (h n : ℝ)⁻¹) * ((s + s : ℝ≥0) : ℝ) *
            ‖gmpKilledL2Operator G U hU (s + s) x -
              gmpKilledL2Operator G U hU (s + s + h n) x‖ := by push_cast; ring
        _ ≤ ((1 / 2 : ℝ) * (h n : ℝ)⁻¹) * (2 * (h n : ℝ) * ‖x‖) := by
          simpa only [mul_assoc] using
            (mul_le_mul_of_nonneg_left hb (show 0 ≤ (1 / 2 : ℝ) * (h n : ℝ)⁻¹ by positivity))
        _ = ‖x‖ := by field_simp
    have hdiv : ‖q n x‖ ≤ ‖x‖ / (s : ℝ) :=
      (le_div_iff₀ hsreal).2 (by simpa only [mul_comm] using hsbound)
    simpa only [div_eq_inv_mul] using hdiv
  have hsub (n : ℕ) (x y : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
      q n (x - y) = q n x - q n y := by
    dsimp only [q, T]
    simp only [map_sub, smul_sub]
    abel
  induction k with
  | zero => exact ⟨f, by simpa only [Function.iterate_zero, id_eq] using tendsto_const_nhds⟩
  | succ k ih =>
    obtain ⟨g, hg⟩ := ih
    obtain ⟨v, hv⟩ := killedL2_dyadic_difference_quotients_converge G U hU s hs g
    change Tendsto (fun n => q n g) atTop (nhds v) at hv
    refine ⟨v, ?_⟩
    have he : Tendsto (fun n => q n ((q n)^[k] f) - q n g) atTop (nhds 0) := by
      apply tendsto_iff_norm_sub_tendsto_zero.2
      simp only [sub_zero]
      have hu : Tendsto (fun n => (s : ℝ)⁻¹ * ‖(q n)^[k] f - g‖) atTop (nhds 0) := by
        simpa only [mul_zero] using tendsto_const_nhds.mul (tendsto_iff_norm_sub_tendsto_zero.1 hg)
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hu
      rw [← hsub]
      exact hbound n _
    have hsum := he.add hv
    simpa only [zero_add, sub_add_cancel, Function.iterate_succ_apply'] using hsum

/-- The actual killed evolution has a decaying equal-step L² increment bound. -/
theorem killedL2_norm_increment_at_n_le
    (U : Set (Vec d)) (hU : IsOpen U) (h : ℝ≥0)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : f ∈ physicalZeroBoundaryL2 U hd ω lam L hω) (n : ℕ) :
    (n : ℝ) * ‖gmpKilledL2Operator G U hU (n • h) f -
      gmpKilledL2Operator G U hU h (gmpKilledL2Operator G U hU (n • h) f)‖ ^ 2 ≤
      ‖f‖ ^ 2 := by
  let T := gmpKilledL2Operator G U hU
  let t : ℝ≥0 := n • h
  let g := T t f
  have hself : ⟪g, g⟫_ℝ = ⟪T (t + t) f, f⟫_ℝ := by
    dsimp only [g, T]
    rw [gmpKilledL2Operator_add_time, ContinuousLinearMap.comp_apply]
    exact (gmpKilledL2Operator_isSymmetric G U hU t (T t f) f).symm
  have hcross : ⟪T h g, g⟫_ℝ = ⟪T (t + t + h) f, f⟫_ℝ := by
    dsimp only [g, T]
    rw [gmpKilledL2Operator_add_time, ContinuousLinearMap.comp_apply,
      gmpKilledL2Operator_add_time, ContinuousLinearMap.comp_apply]
    have hs := gmpKilledL2Operator_isSymmetric G U hU t (T h (T t f)) f
    have hc : T t (T h (T t f)) = T t (T t (T h f)) := by
      apply congrArg (T t)
      dsimp only [T]
      rw [← ContinuousLinearMap.comp_apply, ← gmpKilledL2Operator_add_time,
        ← ContinuousLinearMap.comp_apply, ← gmpKilledL2Operator_add_time, add_comm h t]
    exact hs.symm.trans (congrArg (fun z => ⟪z, f⟫_ℝ) hc)
  have hdisp := gmpKilledL2_norm_sub_sq_le_inner G U hU h g
  rw [inner_sub_left, hself, hcross] at hdisp
  have hcor := killedL2_correlation_increment_at_n_le G U hU h f hf (n + n)
  simp only [add_nsmul, one_nsmul] at hcor
  change ((n + n : ℕ) : ℝ) * (⟪T (t + t) f, f⟫_ℝ -
    ⟪T (t + t + h) f, f⟫_ℝ) ≤ ‖f‖ ^ 2 at hcor
  push_cast at hcor
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  dsimp only [g, t, T] at hdisp hcor ⊢
  nlinarith

/-- Iterating the equal-step estimate bounds a second killed-operator increment. -/
theorem killedL2_second_increment_at_two_n_le
    (U : Set (Vec d)) (hU : IsOpen U) (h : ℝ≥0)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : f ∈ physicalZeroBoundaryL2 U hd ω lam L hω) (n : ℕ) :
    let T := gmpKilledL2Operator G U hU
    let g := T (n • h) f - T h (T (n • h) f)
    (n : ℝ) ^ 2 * ‖T (n • h) g - T h (T (n • h) g)‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  dsimp only
  let g := gmpKilledL2Operator G U hU (n • h) f -
    gmpKilledL2Operator G U hU h (gmpKilledL2Operator G U hU (n • h) f)
  have hg : g ∈ physicalZeroBoundaryL2 U hd ω lam L hω := by
    apply (physicalZeroBoundaryL2 U hd ω lam L hω).sub_mem
    · exact gmpKilledL2_mem_zeroBoundaryL2 G U hU (n • h) f
    · exact gmpKilledL2_mem_zeroBoundaryL2 G U hU h _
  have hfirst := killedL2_norm_increment_at_n_le G U hU h f hf n
  have hsecond := killedL2_norm_increment_at_n_le G U hU h g hg n
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hm := mul_le_mul_of_nonneg_left hsecond hn
  dsimp only [g] at hfirst hm
  nlinarith

/-- Every iterated equal-step killed-operator difference satisfies the
corresponding power bound on the actual interior L² space. -/
theorem killedL2_iterated_increment_at_n_le
    (U : Set (Vec d)) (hU : IsOpen U) (h : ℝ≥0)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : f ∈ physicalZeroBoundaryL2 U hd ω lam L hω) (n k : ℕ) :
    let T := gmpKilledL2Operator G U hU
    let D := fun g => T (n • h) g - T h (T (n • h) g)
    (n : ℝ) ^ k * ‖D^[k] f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  dsimp only
  let D := fun g => gmpKilledL2Operator G U hU (n • h) g -
    gmpKilledL2Operator G U hU h (gmpKilledL2Operator G U hU (n • h) g)
  change (n : ℝ) ^ k * ‖D^[k] f‖ ^ 2 ≤ ‖f‖ ^ 2
  induction k generalizing f with
  | zero => simp only [pow_zero, Function.iterate_zero, id_eq, one_mul, le_refl]
  | succ k ih =>
    have hDf : D f ∈ physicalZeroBoundaryL2 U hd ω lam L hω := by
      apply (physicalZeroBoundaryL2 U hd ω lam L hω).sub_mem
      · exact gmpKilledL2_mem_zeroBoundaryL2 G U hU (n • h) f
      · exact gmpKilledL2_mem_zeroBoundaryL2 G U hU h _
    have hstep : (n : ℝ) * ‖D f‖ ^ 2 ≤ ‖f‖ ^ 2 :=
      killedL2_norm_increment_at_n_le G U hU h f hf n
    have hk := ih (D f) hDf
    rw [Function.iterate_succ_apply, pow_succ]
    calc
      (n : ℝ) ^ k * (n : ℝ) * ‖D^[k] (D f)‖ ^ 2 =
          (n : ℝ) * ((n : ℝ) ^ k * ‖D^[k] (D f)‖ ^ 2) := by ring
      _ ≤ (n : ℝ) * ‖D f‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hk (Nat.cast_nonneg n)
      _ ≤ ‖f‖ ^ 2 := hstep

/-- Mixed equal-step differences retain the product of their individual decay bounds. -/
theorem killedL2_mixed_increment_le
    (U : Set (Vec d)) (hU : IsOpen U)
    (h : ℕ → ℝ≥0) (n : ℕ → ℕ)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : f ∈ physicalZeroBoundaryL2 U hd ω lam L hω) (k : ℕ) :
    let T := gmpKilledL2Operator G U hU
    let v : ℕ → Lp ℝ 2 (physicalReversibleMeasure ω hd lam) := fun m => Nat.rec f (fun j g =>
      T (n j • h j) g - T (h j) (T (n j • h j) g)) m
    (∏ j ∈ Finset.range k, (n j : ℝ)) * ‖v k‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  dsimp only
  let T := gmpKilledL2Operator G U hU
  let v : ℕ → Lp ℝ 2 (physicalReversibleMeasure ω hd lam) := fun m =>
    Nat.rec f (fun j g => T (n j • h j) g - T (h j) (T (n j • h j) g)) m
  change (∏ j ∈ Finset.range k, (n j : ℝ)) * ‖v k‖ ^ 2 ≤ ‖f‖ ^ 2
  have hv (m : ℕ) : v m ∈ physicalZeroBoundaryL2 U hd ω lam L hω := by
    cases m with
    | zero => exact hf
    | succ m =>
      apply (physicalZeroBoundaryL2 U hd ω lam L hω).sub_mem
      · exact gmpKilledL2_mem_zeroBoundaryL2 G U hU (n m • h m) (v m)
      · exact gmpKilledL2_mem_zeroBoundaryL2 G U hU (h m) _
  induction k with
  | zero => simp [v]
  | succ k ih =>
    have hstep := killedL2_norm_increment_at_n_le G U hU (h k) (v k) (hv k) (n k)
    have hp : 0 ≤ ∏ j ∈ Finset.range k, (n j : ℝ) :=
      Finset.prod_nonneg (fun j hj => Nat.cast_nonneg (n j))
    rw [Finset.prod_range_succ]
    calc
      (∏ j ∈ Finset.range k, (n j : ℝ)) * (n k : ℝ) * ‖v (k + 1)‖ ^ 2 =
          (∏ j ∈ Finset.range k, (n j : ℝ)) *
            ((n k : ℝ) * ‖v (k + 1)‖ ^ 2) := by ring
      _ ≤ (∏ j ∈ Finset.range k, (n j : ℝ)) * ‖v k‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ hp
        exact hstep
      _ ≤ ‖f‖ ^ 2 := ih

/-- Iterated killed semigroup differences have linear decay at each mesh step. -/
theorem killedL2_iterated_linear_increment_at_n_le
    (U : Set (Vec d)) (hU : IsOpen U) (h : ℝ≥0)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : f ∈ physicalZeroBoundaryL2 U hd ω lam L hω) (n k : ℕ) :
    let T := gmpKilledL2Operator G U hU
    let D := fun g => T (n • h) g - T ((n + 1) • h) g
    (n : ℝ) ^ k * ‖D^[k] f‖ ≤ ‖f‖ := by
  dsimp only
  let D := fun g => gmpKilledL2Operator G U hU (n • h) g -
    gmpKilledL2Operator G U hU ((n + 1) • h) g
  change (n : ℝ) ^ k * ‖D^[k] f‖ ≤ ‖f‖
  induction k generalizing f with
  | zero => simp only [pow_zero, Function.iterate_zero, id_eq, one_mul, le_refl]
  | succ k ih =>
    have hDf : D f ∈ physicalZeroBoundaryL2 U hd ω lam L hω := by
      apply (physicalZeroBoundaryL2 U hd ω lam L hω).sub_mem
      · exact gmpKilledL2_mem_zeroBoundaryL2 G U hU (n • h) f
      · exact gmpKilledL2_mem_zeroBoundaryL2 G U hU ((n + 1) • h) f
    have hstep : (n : ℝ) * ‖D f‖ ≤ ‖f‖ :=
      killedL2_linear_increment_at_n_le G U hU h f hf n
    have hk := ih (D f) hDf
    rw [Function.iterate_succ_apply, pow_succ]
    calc
      (n : ℝ) ^ k * (n : ℝ) * ‖D^[k] (D f)‖ =
          (n : ℝ) * ((n : ℝ) ^ k * ‖D^[k] (D f)‖) := by ring
      _ ≤ (n : ℝ) * ‖D f‖ :=
        mul_le_mul_of_nonneg_left hk (Nat.cast_nonneg n)
      _ ≤ ‖f‖ := hstep

/-- Mixed killed semigroup differences multiply the linear mesh-step decay. -/
theorem killedL2_mixed_linear_increment_le
    (U : Set (Vec d)) (hU : IsOpen U)
    (h : ℕ → ℝ≥0) (n : ℕ → ℕ)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : f ∈ physicalZeroBoundaryL2 U hd ω lam L hω) (k : ℕ) :
    let T := gmpKilledL2Operator G U hU
    let v : ℕ → Lp ℝ 2 (physicalReversibleMeasure ω hd lam) := fun m => Nat.rec f (fun j g =>
      T (n j • h j) g - T ((n j + 1) • h j) g) m
    (∏ j ∈ Finset.range k, (n j : ℝ)) * ‖v k‖ ≤ ‖f‖ := by
  dsimp only
  let T := gmpKilledL2Operator G U hU
  let v : ℕ → Lp ℝ 2 (physicalReversibleMeasure ω hd lam) := fun m =>
    Nat.rec f (fun j g => T (n j • h j) g - T ((n j + 1) • h j) g) m
  change (∏ j ∈ Finset.range k, (n j : ℝ)) * ‖v k‖ ≤ ‖f‖
  have hv (m : ℕ) : v m ∈ physicalZeroBoundaryL2 U hd ω lam L hω := by
    cases m with
    | zero => exact hf
    | succ m =>
      apply (physicalZeroBoundaryL2 U hd ω lam L hω).sub_mem
      · exact gmpKilledL2_mem_zeroBoundaryL2 G U hU (n m • h m) (v m)
      · exact gmpKilledL2_mem_zeroBoundaryL2 G U hU ((n m + 1) • h m) (v m)
  induction k with
  | zero => simp [v]
  | succ k ih =>
    have hstep := killedL2_linear_increment_at_n_le G U hU (h k) (v k) (hv k) (n k)
    have hp : 0 ≤ ∏ j ∈ Finset.range k, (n j : ℝ) :=
      Finset.prod_nonneg (fun j hj => Nat.cast_nonneg (n j))
    rw [Finset.prod_range_succ]
    calc
      (∏ j ∈ Finset.range k, (n j : ℝ)) * (n k : ℝ) * ‖v (k + 1)‖ =
          (∏ j ∈ Finset.range k, (n j : ℝ)) *
            ((n k : ℝ) * ‖v (k + 1)‖) := by ring
      _ ≤ (∏ j ∈ Finset.range k, (n j : ℝ)) * ‖v k‖ := by
        apply mul_le_mul_of_nonneg_left _ hp
        exact hstep
      _ ≤ ‖f‖ := ih

/-- A zero killed orbit at one time is already zero at half that time.
This uses symmetry of the literal killed evolution, with no reachability premise. -/
theorem killedL2_eq_zero_at_half (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ≥0) (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : gmpKilledL2Operator G U hU t f = 0) :
    gmpKilledL2Operator G U hU (t / 2) f = 0 := by
  have h := gmpKilledL2_inner_eq_half_norm_sq G U hU t f
  rw [hf, inner_zero_left] at h
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp h.symm)

/-- No nonzero interior physical L² datum becomes zero at a finite time.
Repeated symmetry at half times and strong recovery at zero rule out extinction. -/
theorem killedL2_eq_zero_iff (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ≥0) (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : f ∈ physicalZeroBoundaryL2 U hd ω lam L hω) :
    gmpKilledL2Operator G U hU t f = 0 ↔ f = 0 := by
  constructor
  · intro hzero
    have hdyad (n : ℕ) :
        gmpKilledL2Operator G U hU (t * (1 / 2) ^ n) f = 0 := by
      induction n with
      | zero => simpa only [pow_zero, mul_one] using hzero
      | succ n ih =>
        simpa only [pow_succ, mul_assoc, div_eq_mul_inv, one_mul] using
          killedL2_eq_zero_at_half G U hU (t * (1 / 2) ^ n) f ih
    have htime : Tendsto (fun n : ℕ => t * (1 / 2 : ℝ≥0) ^ n) atTop (nhds 0) := by
      simpa only [mul_zero] using
        (tendsto_const_nhds.mul
          (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (1 / 2 : ℝ≥0) < 1)))
    have hlim := (tendsto_gmpKilledL2_at_zero_of_mem G U hU f hf).comp htime
    have heq : (fun n : ℕ => gmpKilledL2 G U hU (t * (1 / 2) ^ n) f) =
        fun _ => 0 := funext hdyad
    change Tendsto (fun n : ℕ => gmpKilledL2 G U hU (t * (1 / 2) ^ n) f)
      atTop (nhds f) at hlim
    rw [heq] at hlim
    exact tendsto_nhds_unique hlim tendsto_const_nhds
  · rintro rfl
    exact map_zero _

/-- The actual killed operator is injective on its exact interior carrier. -/
theorem killedInteriorOperator_injective (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ≥0) : Function.Injective (gmpKilledInteriorOperator G U hU t) := by
  intro f g hfg
  have hzero : gmpKilledL2Operator G U hU t (f.val - g.val) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr (congrArg Subtype.val hfg)
  have hval := (killedL2_eq_zero_iff G U hU t (f.val - g.val)
    ((physicalZeroBoundaryL2 U hd ω lam L hω).sub_mem f.property g.property)).mp hzero
  exact Subtype.ext (sub_eq_zero.mp hval)

/-- Every nonzero interior datum has strictly positive killed self-correlation
at every time, including time zero. This is not positivity improvement. -/
theorem killedL2_inner_pos (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ≥0) (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : f ∈ physicalZeroBoundaryL2 U hd ω lam L hω) (hne : f ≠ 0) :
    0 < inner ℝ (gmpKilledL2Operator G U hU t f) f := by
  rw [gmpKilledL2_inner_eq_half_norm_sq]
  exact sq_pos_of_pos (norm_pos_iff.mpr
    (fun hz => hne ((killedL2_eq_zero_iff G U hU (t / 2) f hf).mp hz)))

/-- Literal multiplication by a measurable support indicator in physical L². -/
def physicalL2SupportProjection (A : Set (Vec d)) (hA : MeasurableSet A)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    Lp ℝ 2 (physicalReversibleMeasure ω hd lam) :=
  ((Lp.memLp f).indicator hA).toLp (A.indicator f)

/-- The support projection retains its literal indicator representative. -/
theorem physicalL2SupportProjection_ae_eq (A : Set (Vec d)) (hA : MeasurableSet A)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    physicalL2SupportProjection A hA f =ᵐ[physicalReversibleMeasure ω hd lam]
      A.indicator f :=
  ((Lp.memLp f).indicator hA).coeFn_toLp

/-- Physical L² functions supported on complementary measurable regions are orthogonal. -/
theorem physicalL2_inner_eq_zero_of_disjoint_support (A : Set (Vec d))
    (f g : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, x ∉ A → f x = 0)
    (hg : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, x ∈ A → g x = 0) :
    inner ℝ f g = 0 := by
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [hf, hg] with x hx hy
  by_cases hxA : x ∈ A
  · simp [hy hxA]
  · simp [hx hxA]

/-- Restriction to a support invariant under the literal killed evolution
does not increase any of its short-time form quotients. Symmetry makes the
complementary component orthogonal, and its remaining form is nonnegative. -/
theorem killedFormDifferenceQuotient_supportProjection_le
    (U : Set (Vec d)) (hU : IsOpen U) (A : Set (Vec d)) (hA : MeasurableSet A)
    (hAinv : ∀ t : ℝ≥0, ∀ v : Lp ℝ 2 (physicalReversibleMeasure ω hd lam),
      (∀ᵐ x ∂physicalReversibleMeasure ω hd lam, x ∉ A → v x = 0) →
      ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
        x ∉ A → gmpKilledL2Operator G U hU t v x = 0)
    (t : ℝ≥0) (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    semigroupFormDifferenceQuotient ω hd lam (gmpKilledEndpointKernel G U hU) t
      (physicalL2SupportProjection A hA f) ≤
      semigroupFormDifferenceQuotient ω hd lam (gmpKilledEndpointKernel G U hU) t f := by
  let g := physicalL2SupportProjection A hA f
  have hrep : g =ᵐ[physicalReversibleMeasure ω hd lam] A.indicator f :=
    physicalL2SupportProjection_ae_eq A hA f
  have hg : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, x ∉ A → g x = 0 := by
    filter_upwards [hrep] with x hx hxA
    rw [hx, Set.indicator_of_notMem hxA]
  have hh : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, x ∈ A → (f - g) x = 0 := by
    filter_upwards [hrep, Lp.coeFn_sub f g] with x hx hsub hxA
    rw [hsub]
    change f x - g x = 0
    rw [hx, Set.indicator_of_mem hxA, sub_self]
  have horth := physicalL2_inner_eq_zero_of_disjoint_support A g (f - g) hg hh
  have hTorth := physicalL2_inner_eq_zero_of_disjoint_support A
    (gmpKilledL2Operator G U hU t g) (f - g) (hAinv t g hg) hh
  have hcross₁ : inner ℝ (g - gmpKilledL2Operator G U hU t g) (f - g) = 0 := by
    rw [inner_sub_left, horth, hTorth, sub_self]
  have hcross₂ : inner ℝ ((f - g) - gmpKilledL2Operator G U hU t (f - g)) g = 0 := by
    have hs : inner ℝ (gmpKilledL2Operator G U hU t (f - g)) g =
        inner ℝ (f - g) (gmpKilledL2Operator G U hU t g) :=
      gmpKilledL2Operator_isSymmetric G U hU t (f - g) g
    rw [inner_sub_left, hs, ← real_inner_comm (f - g) g,
      ← real_inner_comm (f - g) (gmpKilledL2Operator G U hU t g), horth, hTorth, sub_self]
  have hsum : g + (f - g) = f := by abel
  have hvec : (g - gmpKilledL2Operator G U hU t g) +
      ((f - g) - gmpKilledL2Operator G U hU t (f - g)) =
      f - gmpKilledL2Operator G U hU t f := by
    calc
      _ = (g + (f - g)) - (gmpKilledL2Operator G U hU t g +
          gmpKilledL2Operator G U hU t (f - g)) := by abel
      _ = _ := by rw [← map_add, hsum]
  have hsplit : inner ℝ (f - gmpKilledL2Operator G U hU t f) f =
      inner ℝ (g - gmpKilledL2Operator G U hU t g) g +
        inner ℝ ((f - g) - gmpKilledL2Operator G U hU t (f - g)) (f - g) := by
    calc
      _ = inner ℝ ((g - gmpKilledL2Operator G U hU t g) +
          ((f - g) - gmpKilledL2Operator G U hU t (f - g))) (g + (f - g)) := by
        rw [hvec, hsum]
      _ = _ := by simp only [inner_add_left, inner_add_right, hcross₁, hcross₂,
        add_zero, zero_add]
  rw [gmpKilledFormDifferenceQuotient_eq_inner, gmpKilledFormDifferenceQuotient_eq_inner]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  change inner ℝ (g - gmpKilledL2Operator G U hU t g) g ≤ _
  rw [hsplit]
  exact le_add_of_nonneg_right (gmpKilledL2_inner_sub_nonneg G U hU t (f - g))

/-- The literal killed expectations preserve nonnegative physical L² data. -/
theorem killedL2_nonneg (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, 0 ≤ f x) :
    ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      0 ≤ gmpKilledL2Operator G U hU t f x := by
  filter_upwards [gmpKilledL2_ae_eq G U hU t f,
    ae_ae_gmpKilledEndpointKernel_of_ae G U hU t hf] with x hx hn
  change 0 ≤ gmpKilledL2 G U hU t f x
  rw [hx]
  exact integral_nonneg_of_ae hn

/-- Order of physical L² representatives is preserved by the actual killed kernel. -/
theorem killedL2_mono (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0)
    (f g : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hfg : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, f x ≤ g x) :
    ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      gmpKilledL2Operator G U hU t f x ≤ gmpKilledL2Operator G U hU t g x := by
  let := isFiniteKernel_gmpKilledEndpointKernel G U hU t
  filter_upwards [gmpKilledL2_ae_eq G U hU t f, gmpKilledL2_ae_eq G U hU t g,
    ae_ae_gmpKilledEndpointKernel_of_ae G U hU t hfg,
    ae_memLp_gmpKilledEndpointKernel G U hU t f,
    ae_memLp_gmpKilledEndpointKernel G U hU t g] with x hx hy hle hf hg
  change gmpKilledL2 G U hU t f x ≤ gmpKilledL2 G U hU t g x
  rw [hx, hy]
  exact integral_mono_ae (hf.integrable (by norm_num)) (hg.integrable (by norm_num)) hle

/-- A killed zero region for a nonnegative datum is also a zero region for
any signed datum bounded in absolute value by it. -/
theorem killedL2_zero_on_of_abs_le
    (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0)
    (f v : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hbound : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, |v x| ≤ f x)
    (A : Set (Vec d))
    (hzero : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      x ∈ A → gmpKilledL2Operator G U hU t f x = 0) :
    ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      x ∈ A → gmpKilledL2Operator G U hU t v x = 0 := by
  have hupper : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, v x ≤ f x := by
    filter_upwards [hbound] with x hx
    exact (le_abs_self _).trans hx
  have hlower : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, (-v) x ≤ f x := by
    filter_upwards [hbound, Lp.coeFn_neg v] with x hx hv
    rw [hv]
    exact (neg_le_abs _).trans hx
  have hupper' := killedL2_mono G U hU t v f hupper
  have hlower' := killedL2_mono G U hU t (-v) f hlower
  have hneg : gmpKilledL2Operator G U hU t (-v) =
      -gmpKilledL2Operator G U hU t v := map_neg _ _
  filter_upwards [hupper', hlower', hzero,
    Lp.coeFn_neg (gmpKilledL2Operator G U hU t v)] with x hu hl hz hn hxA
  rw [hneg, hn, hz hxA] at hl
  rw [hz hxA] at hu
  change -(gmpKilledL2Operator G U hU t v x) ≤ 0 at hl
  linarith

/-- A zero killed expectation of a nonnegative datum also annihilates every
signed datum supported on its essential support. -/
theorem killedL2_zero_on_of_support
    (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0)
    (f v : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, 0 ≤ f x)
    (hv : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, f x = 0 → v x = 0)
    (A : Set (Vec d))
    (hzero : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      x ∈ A → gmpKilledL2Operator G U hU t f x = 0) :
    ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      x ∈ A → gmpKilledL2Operator G U hU t v x = 0 := by
  letI := isFiniteKernel_gmpKilledEndpointKernel G U hU t
  filter_upwards [gmpKilledL2_ae_eq G U hU t f,
    gmpKilledL2_ae_eq G U hU t v,
    ae_ae_gmpKilledEndpointKernel_of_ae G U hU t hf,
    ae_ae_gmpKilledEndpointKernel_of_ae G U hU t hv,
    ae_memLp_gmpKilledEndpointKernel G U hU t f, hzero]
    with x hfe hve hfn hvn hfi hz hxA
  have hIntegral : (∫ y, f y ∂gmpKilledEndpointKernel G U hU t x) = 0 := by
    rw [← hfe]
    exact hz hxA
  have hfzero := (integral_eq_zero_iff_of_nonneg_ae hfn
    (hfi.integrable (by norm_num))).mp hIntegral
  change gmpKilledL2 G U hU t v x = 0
  rw [hve]
  apply integral_eq_zero_of_ae
  filter_upwards [hfzero, hvn] with y hy hyv
  exact hyv hy

/-- If a nonnegative datum cannot leave its own support under a killed
operator, that support is invariant for every signed L² input. -/
theorem killedL2_support_invariant_of_self
    (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, 0 ≤ f x)
    (hself : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      f x = 0 → gmpKilledL2Operator G U hU t f x = 0)
    (v : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hv : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, f x = 0 → v x = 0) :
    ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      f x = 0 → gmpKilledL2Operator G U hU t v x = 0 := by
  exact killedL2_zero_on_of_support G U hU t f v hf hv {x | f x = 0} hself

/-- If a nonnegative interior datum has zero killed expectation on a measurable
region, it was already zero there. Restriction to that region and strict
self-correlation rule out any nonzero portion of the original datum. -/
theorem killedL2_input_zero_on_of_zero_on
    (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : f ∈ physicalZeroBoundaryL2 U hd ω lam L hω)
    (hfnonneg : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, 0 ≤ f x)
    (A : Set (Vec d)) (hA : MeasurableSet A)
    (hzero : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      x ∈ A → gmpKilledL2Operator G U hU t f x = 0) :
    ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, x ∈ A → f x = 0 := by
  let g := physicalL2SupportProjection A hA f
  have hrep : g =ᵐ[physicalReversibleMeasure ω hd lam] A.indicator f :=
    physicalL2SupportProjection_ae_eq A hA f
  have hgnonneg : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, 0 ≤ g x := by
    filter_upwards [hrep, hfnonneg] with x hx hn
    rw [hx]
    by_cases hxA : x ∈ A <;> simp [hxA, hn]
  have hgle : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, g x ≤ f x := by
    filter_upwards [hrep, hfnonneg] with x hx hn
    rw [hx]
    by_cases hxA : x ∈ A <;> simp [hxA, hn]
  have hgin : g ∈ physicalZeroBoundaryL2 U hd ω lam L hω := by
    apply (mem_physicalZeroBoundaryL2_iff_zero_off U hU hd ω lam L hω g).mpr
    filter_upwards [hrep,
      (mem_physicalZeroBoundaryL2_iff_zero_off U hU hd ω lam L hω f).mp hf]
      with x hx hfU hxU
    rw [hx]
    by_cases hxA : x ∈ A <;> simp [hxA, hfU hxU]
  have hTzero : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      x ∈ A → gmpKilledL2Operator G U hU t g x = 0 := by
    filter_upwards [killedL2_nonneg G U hU t g hgnonneg,
      killedL2_mono G U hU t g f hgle, hzero] with x hn hle hz hxA
    exact le_antisymm (hle.trans_eq (hz hxA)) hn
  have hgAc : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, x ∉ A → g x = 0 := by
    filter_upwards [hrep] with x hx hxA
    rw [hx, Set.indicator_of_notMem hxA]
  have hinner : inner ℝ (gmpKilledL2Operator G U hU t g) g = 0 := by
    rw [real_inner_comm]
    exact physicalL2_inner_eq_zero_of_disjoint_support A g
      (gmpKilledL2Operator G U hU t g) hgAc hTzero
  have hgzero : g = 0 := by
    by_contra hne
    exact (killedL2_inner_pos G U hU t g hgin hne).ne' hinner
  have hgpoint : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, g x = 0 := by
    rw [hgzero]
    exact Lp.coeFn_zero ℝ 2 _
  filter_upwards [hrep, hgpoint] with x hx hgx hxA
  rw [hx, Set.indicator_of_mem hxA] at hgx
  exact hgx

/-- A nonnegative interior physical L² datum retains its essential support
at every time under the literal killed semigroup. -/
theorem killedL2_support_inclusion
    (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : f ∈ physicalZeroBoundaryL2 U hd ω lam L hω)
    (hfnonneg : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, 0 ≤ f x) :
    ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      f x ≠ 0 → gmpKilledL2Operator G U hU t f x ≠ 0 := by
  let A := {x : Vec d | gmpKilledL2Operator G U hU t f x = 0}
  have hA : MeasurableSet A :=
    (measurableSet_singleton (0 : ℝ)).preimage
      (Lp.stronglyMeasurable (gmpKilledL2Operator G U hU t f)).measurable
  have hz := killedL2_input_zero_on_of_zero_on G U hU t f hf hfnonneg A hA
    (ae_of_all _ fun _ hx => hx)
  filter_upwards [hz] with x hx hfx hTx
  exact hfx (hx hTx)

/-- Essential supports of a nonnegative killed orbit increase with time. This
does not identify the support at a positive time with the full killing domain. -/
theorem killedL2_support_mono_time
    (U : Set (Vec d)) (hU : IsOpen U) (s t : ℝ≥0) (hst : s ≤ t)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hfnonneg : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, 0 ≤ f x) :
    ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      gmpKilledL2Operator G U hU s f x ≠ 0 →
        gmpKilledL2Operator G U hU t f x ≠ 0 := by
  have h := killedL2_support_inclusion G U hU (t - s)
    (gmpKilledL2Operator G U hU s f)
    (gmpKilledL2_mem_zeroBoundaryL2 G U hU s f)
    (killedL2_nonneg G U hU s f hfnonneg)
  have heq : gmpKilledL2Operator G U hU (t - s)
      (gmpKilledL2Operator G U hU s f) = gmpKilledL2Operator G U hU t f := by
    change gmpKilledL2 G U hU (t - s) (gmpKilledL2 G U hU s f) = _
    rw [← gmpKilledL2_add_time, tsub_add_cancel_of_le hst]
    rfl
  simpa only [heq] using h

/-- Invariance of the support at one positive time propagates to all times. -/
theorem killedL2_support_invariant_of_one_time
    (U : Set (Vec d)) (hU : IsOpen U) (a : ℝ≥0) (ha : 0 < a)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, 0 ≤ f x)
    (hself : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      f x = 0 → gmpKilledL2Operator G U hU a f x = 0) :
    ∀ t : ℝ≥0, ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      f x = 0 → gmpKilledL2Operator G U hU t f x = 0 := by
  have hmul (n : ℕ) : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      f x = 0 → gmpKilledL2Operator G U hU ((n + 1 : ℕ) • a) f x = 0 := by
    induction n with
    | zero => simpa using hself
    | succ n ih =>
      have h := killedL2_support_invariant_of_self G U hU a f hf hself
        (gmpKilledL2Operator G U hU ((n + 1 : ℕ) • a) f) ih
      have heq : gmpKilledL2Operator G U hU a
          (gmpKilledL2Operator G U hU ((n + 1 : ℕ) • a) f) =
          gmpKilledL2Operator G U hU ((n + 1 + 1 : ℕ) • a) f := by
        change gmpKilledL2 G U hU a (gmpKilledL2 G U hU ((n + 1 : ℕ) • a) f) = _
        rw [← gmpKilledL2_add_time]
        congr 2
        simp [add_mul, add_comm]
      simpa only [heq, Nat.succ_eq_add_one] using h
  intro t
  obtain ⟨n, hn⟩ := exists_nat_gt (t / a)
  have hbound : t ≤ (n + 1 : ℕ) • a := by
    have hn' : t / a < ((n + 1 : ℕ) : ℝ≥0) := by
      exact hn.trans_le (by exact_mod_cast Nat.le_succ n)
    have := (div_lt_iff₀ ha).mp hn'
    simpa [nsmul_eq_mul] using this.le
  have hm := killedL2_support_mono_time G U hU t ((n + 1 : ℕ) • a) hbound f hf
  filter_upwards [hm, hmul n] with x hx hy hfx
  by_contra hne
  exact hx hne (hy hfx)

/-- Analyticity of the scalar killed-orbit coefficients supplies the missing
forward support implication. The analyticity hypothesis is explicit and is
not asserted here for the killed semigroup. -/
theorem killedL2_positive_time_support_invariant_of_analytic
    (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0) (ht : 0 < t)
    (g : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hg : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, 0 ≤ g x)
    (han : ∀ v : Lp ℝ 2 (physicalReversibleMeasure ω hd lam),
      AnalyticOnNhd ℝ (fun r : ℝ => inner ℝ v
        (gmpKilledL2Operator G U hU r.toNNReal g)) (Set.Ioi 0)) :
    ∀ a : ℝ≥0, ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      gmpKilledL2Operator G U hU t g x = 0 →
        gmpKilledL2Operator G U hU a (gmpKilledL2Operator G U hU t g) x = 0 := by
  intro a
  let f := gmpKilledL2Operator G U hU t g
  let A : Set (Vec d) := {x | f x = 0}
  have hA : MeasurableSet A :=
    (measurableSet_singleton (0 : ℝ)).preimage (Lp.stronglyMeasurable f).measurable
  let w := gmpKilledL2Operator G U hU (a + t) g
  let v := physicalL2SupportProjection A hA w
  have hvrep : v =ᵐ[physicalReversibleMeasure ω hd lam] A.indicator w :=
    physicalL2SupportProjection_ae_eq A hA w
  have hv : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, x ∉ A → v x = 0 := by
    filter_upwards [hvrep] with x hx hxA
    rw [hx, Set.indicator_of_notMem hxA]
  have hzero (r : ℝ) (hr : r ∈ Set.Ioo 0 (t : ℝ)) :
      inner ℝ v (gmpKilledL2Operator G U hU r.toNNReal g) = 0 := by
    apply physicalL2_inner_eq_zero_of_disjoint_support A v _ hv
    have hle : r.toNNReal ≤ t := by
      simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal hr.2.le
    have hm := killedL2_support_mono_time G U hU r.toNNReal t hle g hg
    filter_upwards [hm] with x hx hxA
    have hfx : f x = 0 := hxA
    by_contra hne
    exact hx hne hfx
  have hhalf : (t : ℝ) / 2 ∈ Set.Ioo 0 (t : ℝ) := by
    have ht' : (0 : ℝ) < t := by exact_mod_cast ht
    constructor <;> linarith
  have hnear : (fun r : ℝ => inner ℝ v
      (gmpKilledL2Operator G U hU r.toNNReal g)) =ᶠ[nhds ((t : ℝ) / 2)] 0 := by
    filter_upwards [Ioo_mem_nhds hhalf.1 hhalf.2] with r hr
    exact hzero r hr
  have hall := (han v).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_Ioi hhalf.1 hnear
  have hw : inner ℝ v w = 0 := by
    have hpos : (0 : ℝ) < (a + t : ℝ≥0) := by exact_mod_cast (add_pos_of_nonneg_of_pos (bot_le : 0 ≤ a) ht)
    have h := hall hpos
    simpa only [Real.toNNReal_coe, Pi.zero_apply] using h
  have hwv : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, x ∈ A → (w - v) x = 0 := by
    filter_upwards [hvrep, Lp.coeFn_sub w v] with x hx hsub hxA
    rw [hsub]
    change w x - v x = 0
    rw [hx, Set.indicator_of_mem hxA, sub_self]
  have horth := physicalL2_inner_eq_zero_of_disjoint_support A v (w - v) hv hwv
  have hvzero : v = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    rw [inner_sub_right, hw, zero_sub] at horth
    exact neg_eq_zero.mp horth
  have hvpoint : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, v x = 0 := by
    rw [hvzero]
    exact Lp.coeFn_zero ℝ 2 _
  have heq : gmpKilledL2Operator G U hU a f = w := by
    change gmpKilledL2 G U hU a (gmpKilledL2 G U hU t g) = _
    rw [← gmpKilledL2_add_time]
    rfl
  rw [heq]
  filter_upwards [hvrep, hvpoint] with x hx hz hfx
  have hxA : x ∈ A := hfx
  rw [hx, Set.indicator_of_mem hxA] at hz
  exact hz

/-- At every fixed time, a finite-measure target inside the killing domain has
strictly positive killed mass for physical-almost-every start in that target.
This uses essential-support preservation, with no small-time restriction. -/
theorem killedEndpoint_mass_pos_ae_on_target
    (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0)
    (B : Set (Vec d)) (hB : MeasurableSet B)
    (hBfin : physicalReversibleMeasure ω hd lam B ≠ ∞) (hBU : B ⊆ U) :
    ∀ᵐ x ∂(physicalReversibleMeasure ω hd lam).restrict B,
      0 < gmpKilledEndpointKernel G U hU t x B := by
  let f := indicatorConstLp 2 hB hBfin (1 : ℝ)
  have hrep : f =ᵐ[physicalReversibleMeasure ω hd lam] B.indicator (fun _ => (1 : ℝ)) :=
    indicatorConstLp_coeFn (p := 2) (hs := hB) (hμs := hBfin) (c := (1 : ℝ))
  have hf : f ∈ physicalZeroBoundaryL2 U hd ω lam L hω := by
    apply (mem_physicalZeroBoundaryL2_iff_zero_off U hU hd ω lam L hω f).mpr
    filter_upwards [hrep] with x hx hxU
    rw [hx, Set.indicator_of_notMem (fun hxB => hxU (hBU hxB))]
  have hfn : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, 0 ≤ f x := by
    filter_upwards [hrep] with x hx
    rw [hx]
    by_cases hxB : x ∈ B <;> simp [hxB]
  apply (ae_restrict_iff' hB).mpr
  filter_upwards [hrep, killedL2_support_inclusion G U hU t f hf hfn,
    gmpKilledL2_indicatorConst_ae_eq G U hU t B hB hBfin (1 : ℝ)]
    with x hx hsupport houtput hxB
  have hfx : f x ≠ 0 := by
    rw [hx, Set.indicator_of_mem hxB]
    exact one_ne_zero
  apply pos_iff_ne_zero.mpr
  intro hmass
  apply hsupport hfx
  rw [houtput, hmass, ENNReal.toReal_zero, zero_mul]

/-- The actual killed endpoint mass is exactly the closed fixed-center block
mass, including time zero and the small terminal ball. -/
theorem killedEndpoint_meshBall_eq_meshPiece (ε : ℝ) (τ : ℝ≥0)
    (c : ℕ → Vec d) (k : ℕ) (x : Vec d) :
    gmpKilledEndpointKernel G (meshBall lam (ε / 2) (c k))
      (isOpen_meshBall lam (ε / 2) (c k)) τ x
      (meshBall lam (ε / 16) (c (k + 1))) =
        G.pathLaw x (meshPiece lam ε τ c k) := by
  rw [gmpKilledEndpointKernel_apply,
    Measure.map_apply (measurable_pathPosition τ)
      (isOpen_meshBall lam (ε / 16) (c (k + 1))).measurableSet,
    Measure.restrict_apply (((isOpen_meshBall lam (ε / 16) (c (k + 1))).measurableSet).preimage
      (measurable_pathPosition τ))]
  congr 1
  ext γ
  change (euclideanNorm (lam • γ τ - c (k + 1)) < ε / 16 ∧
    (τ : ℝ≥0∞) < Diffusion.localityExitTime (meshBall lam (ε / 2) (c k)) γ) ↔
    (∀ s : ℝ≥0, s ≤ τ → euclideanNorm (lam • γ s - c k) < ε / 2) ∧
      euclideanNorm (lam • γ τ - c (k + 1)) < ε / 16
  rw [lt_localityExitTime_iff _ (isOpen_meshBall lam (ε / 2) (c k)) γ τ]
  exact and_comm

/-- Every interior starting point has positive actual survival probability at
some strictly positive time below any prescribed horizon. -/
theorem exists_pos_lt_killed_mass_ne_zero (U : Set (Vec d)) (hU : IsOpen U)
    (t : ℝ≥0) (ht : 0 < t) (x : Vec d) (hx : x ∈ U) :
    ∃ s : ℝ≥0, 0 < s ∧ s < t ∧
      gmpKilledEndpointKernel G U hU s x Set.univ ≠ 0 := by
  have hlim := tendsto_integral_gmpKilledEndpointKernel_at_zero G U hU x hx
    (fun _ => (1 : ℝ)) continuous_const 1 (by intro y; norm_num)
  have hpos : ∀ᶠ s : ℝ≥0 in nhds 0,
      0 < ∫ y, (1 : ℝ) ∂gmpKilledEndpointKernel G U hU s x :=
    hlim.eventually (Ioi_mem_nhds zero_lt_one)
  obtain ⟨a, ha, hgood⟩ := NNReal.nhds_zero_basis.mem_iff.mp hpos
  let s := min a t / 2
  have hs : 0 < s := half_pos (lt_min ha ht)
  have hsmall : s < min a t := half_lt_self (lt_min ha ht)
  refine ⟨s, hs, hsmall.trans_le (min_le_right a t), ?_⟩
  intro hz
  have h := hgood (hsmall.trans_le (min_le_left a t))
  change 0 < ∫ y, (1 : ℝ) ∂gmpKilledEndpointKernel G U hU s x at h
  have hzero : gmpKilledEndpointKernel G U hU s x = 0 :=
    Measure.measure_univ_eq_zero.mp hz
  simp only [hzero, integral_zero_measure, lt_self_iff_false] at h

/-- The actual force-and-potential weighted reference measure has exactly the
same positive measurable sets as Lebesgue measure. -/
theorem physicalReversibleMeasure_pos_iff_volume (B : Set (Vec d)) :
    0 < physicalReversibleMeasure ω hd lam B ↔ 0 < volume B := by
  have hdensity : {x : Vec d | ENNReal.ofReal (physicalReversibleDensity ω hd lam x) ≠ 0} =
      Set.univ := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact (ENNReal.ofReal_pos.mpr (physicalReversibleDensity_pos ω hd lam x)).ne'
  have hz : physicalReversibleMeasure ω hd lam B = 0 ↔ volume B = 0 := by
    simpa only [physicalReversibleMeasure, hdensity, Set.univ_inter] using
      (withDensity_apply_eq_zero (μ := (volume : Measure (Vec d)))
        (f := fun x => ENNReal.ofReal (physicalReversibleDensity ω hd lam x)) (s := B)
        (ENNReal.measurable_ofReal.comp
          (physicalReversibleDensity_continuous ω hd lam).measurable))
  rw [pos_iff_ne_zero, pos_iff_ne_zero]
  exact not_congr hz

/-- Physical-a.e. assertions on any measurable domain are equivalent to
Lebesgue-a.e. assertions there, with the actual force and potential density. -/
theorem physicalReversibleMeasure_restrict_ae_iff_volume (B : Set (Vec d))
    (hB : MeasurableSet B) (p : Vec d → Prop) :
    (∀ᵐ y ∂(physicalReversibleMeasure ω hd lam).restrict B, p y) ↔
      ∀ᵐ y ∂(volume : Measure (Vec d)).restrict B, p y := by
  rw [ae_restrict_iff' hB, ae_restrict_iff' hB]
  exact SpatialDirichlet.ae_withDensity_iff_volume_of_continuous_pos
    (physicalReversibleDensity ω hd lam) (physicalReversibleDensity_continuous ω hd lam)
    (physicalReversibleDensity_pos ω hd lam) _

/-- Two-valued members of the actual weighted weak-gradient graph are
constant physical-almost-everywhere throughout each nondegenerate mesh ball. -/
theorem physicalSobolev_twoValue_rigidity_meshBall {radius : ℝ}
    (hlam : 0 < lam) (hradius : 0 < radius) (center : Vec d)
    (u : SpatialDirichlet.WeightedSobolevGraph (EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam))
    (hvalues : ∀ᵐ x ∂(physicalReversibleMeasure ω hd lam).restrict
      (meshBall lam radius center), u.value x = 0 ∨ u.value x = 1) :
    (u.value =ᵐ[(physicalReversibleMeasure ω hd lam).restrict
      (meshBall lam radius center)] fun _ => 0) ∨
      (u.value =ᵐ[(physicalReversibleMeasure ω hd lam).restrict
        (meshBall lam radius center)] fun _ => 1) := by
  have hU := meshBall_isOpenBoundedConvexDomain hlam hradius center
  have hvol := (physicalReversibleMeasure_restrict_ae_iff_volume
    (ω := ω) (hd := hd) (lam := lam) _ hU.measurableSet _).mp hvalues
  have hrig := weightedSobolevGraph_twoValue_rigidity
    (physicalForceWeight hd lam) (physicalForceWeight_continuous hd lam)
    (physicalForceWeight_pos hd lam) hU (volume_meshBall_pos hlam hradius center)
    hU.volume_lt_top u hvol
  exact hrig.imp
    ((physicalReversibleMeasure_restrict_ae_iff_volume _ hU.measurableSet _).mpr)
    ((physicalReversibleMeasure_restrict_ae_iff_volume _ hU.measurableSet _).mpr)

/-- A set whose indicator is represented by the actual weighted Sobolev graph
is either null or conull in the connected mesh domain. Membership of invariant
supports in this graph is a separate analytic obligation. -/
theorem physicalSobolev_indicator_dichotomy_meshBall {radius : ℝ}
    (hlam : 0 < lam) (hradius : 0 < radius) (center : Vec d) (A : Set (Vec d))
    (u : SpatialDirichlet.WeightedSobolevGraph (EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam))
    (hrep : u.value =ᵐ[(physicalReversibleMeasure ω hd lam).restrict
      (meshBall lam radius center)] A.indicator (fun _ => (1 : ℝ))) :
    (physicalReversibleMeasure ω hd lam).restrict (meshBall lam radius center) A = 0 ∨
      (physicalReversibleMeasure ω hd lam).restrict (meshBall lam radius center) Aᶜ = 0 := by
  have hvalues : ∀ᵐ x ∂(physicalReversibleMeasure ω hd lam).restrict
      (meshBall lam radius center), u.value x = 0 ∨ u.value x = 1 := by
    filter_upwards [hrep] with x hx
    rw [hx]
    by_cases hxA : x ∈ A <;> simp [hxA]
  rcases physicalSobolev_twoValue_rigidity_meshBall hlam hradius center u hvalues
    with hz | ho
  · left
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hrep, hz] with x hx hz hxA
    simp only [Set.indicator_of_mem hxA, hz] at hx
    exact zero_ne_one hx
  · right
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hrep, ho] with x hx ho hxA
    simp only [Set.mem_compl_iff] at hxA
    simp only [Set.indicator_of_notMem hxA, ho] at hx
    exact one_ne_zero hx

/-- Bounded actual killed form quotients exclude nontrivial indicators on any
connected mesh ball where the datum agrees with that indicator. The quotient
bound must still be proved for any proposed invariant-support datum. -/
theorem killedFormBound_indicator_dichotomy_meshBall
    (U : Set (Vec d)) (hU : IsOpen U) {radius : ℝ}
    (hlam : 0 < lam) (hradius : 0 < radius) (center : Vec d) (A : Set (Vec d))
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : ∃ C : ℝ, ∀ t : ℝ≥0, 0 < t → semigroupFormDifferenceQuotient ω hd lam
      (gmpKilledEndpointKernel G U hU) t f ≤ C)
    (hrep : f =ᵐ[(physicalReversibleMeasure ω hd lam).restrict
      (meshBall lam radius center)] A.indicator (fun _ => (1 : ℝ))) :
    (physicalReversibleMeasure ω hd lam).restrict (meshBall lam radius center) A = 0 ∨
      (physicalReversibleMeasure ω hd lam).restrict (meshBall lam radius center) Aᶜ = 0 := by
  have hH1 := physicalH1Member_of_bounded_gmpKilledFormDifferenceQuotient G U hU f hf
  obtain ⟨u, hu⟩ := (physicalH1Member_iff_exists_graph ω hd lam f).mp hH1
  apply physicalSobolev_indicator_dichotomy_meshBall hlam hradius center A u
  filter_upwards [ae_restrict_of_ae hu, hrep] with x hx hy
  exact hx.trans hy

/-- An invariant support is locally null or conull wherever a bounded-form
cutoff equals one. The cutoff bound concerns the original datum, rather than
its potentially discontinuous restriction to the invariant support. -/
theorem invariantSupport_dichotomy_meshBall
    (U : Set (Vec d)) (hU : IsOpen U) (A : Set (Vec d)) (hA : MeasurableSet A)
    (hAinv : ∀ t : ℝ≥0, ∀ v : Lp ℝ 2 (physicalReversibleMeasure ω hd lam),
      (∀ᵐ x ∂physicalReversibleMeasure ω hd lam, x ∉ A → v x = 0) →
      ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
        x ∉ A → gmpKilledL2Operator G U hU t v x = 0)
    {radius : ℝ} (hlam : 0 < lam) (hradius : 0 < radius) (center : Vec d)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : ∃ C : ℝ, ∀ t : ℝ≥0, 0 < t → semigroupFormDifferenceQuotient ω hd lam
      (gmpKilledEndpointKernel G U hU) t f ≤ C)
    (hfone : f =ᵐ[(physicalReversibleMeasure ω hd lam).restrict
      (meshBall lam radius center)] fun _ => (1 : ℝ)) :
    (physicalReversibleMeasure ω hd lam).restrict (meshBall lam radius center) A = 0 ∨
      (physicalReversibleMeasure ω hd lam).restrict (meshBall lam radius center) Aᶜ = 0 := by
  apply killedFormBound_indicator_dichotomy_meshBall G U hU hlam hradius center A
    (physicalL2SupportProjection A hA f)
  · obtain ⟨C, hC⟩ := hf
    exact ⟨C, fun t ht => (killedFormDifferenceQuotient_supportProjection_le
      G U hU A hA hAinv t f).trans (hC t ht)⟩
  · filter_upwards [ae_restrict_of_ae (physicalL2SupportProjection_ae_eq A hA f),
      hfone] with x hx hone
    rw [hx]
    by_cases hxA : x ∈ A <;> simp [hxA, hone]

/-- Compactly contained mesh balls see every invariant measurable support as
null or conull. A literal smooth zero-boundary cutoff supplies the form bound. -/
theorem invariantSupport_dichotomy_meshBall_of_closure_subset
    (U : Set (Vec d)) (hU : IsOpen U) (A : Set (Vec d)) (hA : MeasurableSet A)
    (hAinv : ∀ t : ℝ≥0, ∀ v : Lp ℝ 2 (physicalReversibleMeasure ω hd lam),
      (∀ᵐ x ∂physicalReversibleMeasure ω hd lam, x ∉ A → v x = 0) →
      ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
        x ∉ A → gmpKilledL2Operator G U hU t v x = 0)
    {radius : ℝ} (hlam : 0 < lam) (hradius : 0 < radius) (center : Vec d)
    (hBU : closure (meshBall lam radius center) ⊆ U) :
    (physicalReversibleMeasure ω hd lam).restrict (meshBall lam radius center) A = 0 ∨
      (physicalReversibleMeasure ω hd lam).restrict (meshBall lam radius center) Aᶜ = 0 := by
  have hball := meshBall_isOpenBoundedConvexDomain hlam hradius center
  obtain ⟨χ, hχ, hχc, hχU, hχone⟩ := PDE.TraceLane.exists_cutoff_near_compact
    hball.isBoundedDomain.isBounded.isCompact_closure hU hBU
  have htest : IsSpatialTest U χ := ⟨hχ, hχc, hχU⟩
  let u := physicalH1SmoothTest hd lam χ hχ hχc
  have hu : u ∈ physicalH1ZeroBoundary U hd lam :=
    physicalH1SmoothTest_mem_zeroBoundary U hd lam χ htest
  let f := gmpPhysicalH1Value hd ω lam L hω u
  have hrep : f =ᵐ[physicalReversibleMeasure ω hd lam] χ := by
    filter_upwards [gmpPhysicalH1Value_ae_eq hd ω lam L hω u,
      physicalZeroBoundaryValue_ae_eq U hd ω lam L hω ⟨u, hu⟩,
      physicalZeroBoundaryValue_smoothTest_ae_eq U hd ω lam L hω χ htest]
      with x hx hy hz
    exact hx.trans (hy.symm.trans hz)
  apply invariantSupport_dichotomy_meshBall G U hU A hA hAinv hlam hradius center f
  · exact ⟨physicalH1FormEnergy ω hd lam (physicalH1SpaceRepresentative hd lam u),
      fun t ht => gmpKilledFormDifferenceQuotient_le_of_zeroBoundary G U hU t ht u hu⟩
  · filter_upwards [ae_restrict_of_ae hrep,
      ae_restrict_mem (isOpen_meshBall lam radius center).measurableSet] with x hx hxB
    exact hx.trans ((hχone x (subset_closure hxB)).self_of_nhds)

/-- A strictly smaller concentric mesh ball has its closure in the larger ball. -/
theorem closure_meshBall_subset_of_lt {radius R : ℝ} (h : radius < R)
    (center : Vec d) :
    closure (meshBall lam radius center) ⊆ meshBall lam R center := by
  have hc : IsClosed {x : Vec d | euclideanNorm (lam • x - center) ≤ radius} :=
    isClosed_le (continuous_euclideanNorm.comp
      ((continuous_const.fun_smul continuous_id).sub continuous_const)) continuous_const
  have hsub : meshBall lam radius center ⊆
      {x : Vec d | euclideanNorm (lam • x - center) ≤ radius} := by
    intro x hx
    change euclideanNorm (lam • x - center) ≤ radius
    exact le_of_lt (show euclideanNorm (lam • x - center) < radius from hx)
  have hcl := closure_minimal hsub hc
  exact fun x hx => lt_of_le_of_lt (hcl hx) h

/-- Countably many compactly contained concentric balls exhaust the literal
open mesh ball, including points arbitrarily close to its boundary. -/
theorem meshBall_eq_iUnion_inner {R : ℝ} (hR : 0 < R) (center : Vec d) :
    meshBall lam R center =
      ⋃ n : ℕ, meshBall lam (R - R / ((n : ℝ) + 2)) center := by
  ext x
  constructor
  · intro hx
    have hgap : 0 < R - euclideanNorm (lam • x - center) := sub_pos.mpr hx
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (div_pos hgap hR)
    have hrec : 1 / ((n : ℝ) + 2) <
        (R - euclideanNorm (lam • x - center)) / R :=
      (one_div_le_one_div_of_le (by positivity) (by linarith)).trans_lt hn
    have hsmall : R / ((n : ℝ) + 2) < R - euclideanNorm (lam • x - center) := by
      have hm := (mul_lt_mul_of_pos_left hrec hR)
      simpa only [mul_one_div, mul_div_cancel₀ _ hR.ne'] using hm
    exact Set.mem_iUnion.mpr ⟨n, by change euclideanNorm (lam • x - center) < _; linarith⟩
  · intro hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    exact hn.trans (sub_lt_self R (div_pos hR (by positivity)))

/-- Local null/conull choices agree on a countable cover sharing a positive
core; their common choice is null/conull on the whole union. -/
theorem restrict_dichotomy_iUnion_of_common_core {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (B : ℕ → Set α) (hcore : ∀ n, B 0 ⊆ B n)
    (hpos : 0 < μ (B 0)) (A : Set α) (hA : MeasurableSet A)
    (hlocal : ∀ n, μ.restrict (B n) A = 0 ∨ μ.restrict (B n) Aᶜ = 0) :
    μ.restrict (⋃ n, B n) A = 0 ∨ μ.restrict (⋃ n, B n) Aᶜ = 0 := by
  have hglue (S : Set α) (hS : MeasurableSet S)
      (hz : ∀ n, μ.restrict (B n) S = 0) : μ.restrict (⋃ n, B n) S = 0 := by
    rw [Measure.restrict_apply hS, Set.inter_iUnion]
    exact measure_iUnion_null (fun n => by rw [← Measure.restrict_apply hS]; exact hz n)
  have hboth (hz : μ.restrict (B 0) A = 0)
      (ho : μ.restrict (B 0) Aᶜ = 0) : False := by
    have htotal := measure_add_measure_compl (μ := μ.restrict (B 0)) hA
    rw [hz, ho, zero_add, Measure.restrict_apply_univ] at htotal
    exact hpos.ne' htotal.symm
  rcases hlocal 0 with hz | ho
  · left
    apply hglue A hA
    intro n
    rcases hlocal n with hn | hn
    · exact hn
    · exact (hboth hz (le_antisymm
        (((Measure.restrict_mono_set μ (hcore n)) Aᶜ).trans_eq hn) bot_le)).elim
  · right
    apply hglue Aᶜ hA.compl
    intro n
    rcases hlocal n with hn | hn
    · exact (hboth (le_antisymm
        (((Measure.restrict_mono_set μ (hcore n)) A).trans_eq hn) bot_le) ho).elim
    · exact hn

/-- Every measurable support invariant under the actual killed evolution is
null or conull throughout its mesh killing ball. The local Sobolev argument is
exhausted to the boundary; no global indicator is assumed to have zero trace. -/
theorem invariantSupport_dichotomy_killing_meshBall {R : ℝ}
    (hlam : 0 < lam) (hR : 0 < R) (center : Vec d)
    (A : Set (Vec d)) (hA : MeasurableSet A)
    (hAinv : ∀ t : ℝ≥0, ∀ v : Lp ℝ 2 (physicalReversibleMeasure ω hd lam),
      (∀ᵐ x ∂physicalReversibleMeasure ω hd lam, x ∉ A → v x = 0) →
      ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
        x ∉ A → gmpKilledL2Operator G (meshBall lam R center)
          (isOpen_meshBall lam R center) t v x = 0) :
    (physicalReversibleMeasure ω hd lam).restrict (meshBall lam R center) A = 0 ∨
      (physicalReversibleMeasure ω hd lam).restrict (meshBall lam R center) Aᶜ = 0 := by
  let r : ℕ → ℝ := fun n => R - R / ((n : ℝ) + 2)
  have hrpos (n : ℕ) : 0 < r n :=
    sub_pos.mpr (div_lt_self hR (by have := Nat.cast_nonneg (α := ℝ) n; linarith))
  have hrlt (n : ℕ) : r n < R := sub_lt_self R (div_pos hR (by positivity))
  have hcore (n : ℕ) : meshBall lam (r 0) center ⊆ meshBall lam (r n) center := by
    have hdiv : R / ((n : ℝ) + 2) ≤ R / (2 : ℝ) :=
      div_le_div_of_nonneg_left hR.le (by norm_num)
        (le_add_of_nonneg_left (Nat.cast_nonneg n))
    intro x hx
    have hx' : euclideanNorm (lam • x - center) < R - R / 2 := by
      simpa only [r, Nat.cast_zero, zero_add, meshBall, Set.mem_ofPred_eq] using hx
    exact hx'.trans_le (sub_le_sub_left hdiv R)
  rw [meshBall_eq_iUnion_inner hR center]
  apply restrict_dichotomy_iUnion_of_common_core _ (fun n => meshBall lam (r n) center)
    hcore
  · exact (physicalReversibleMeasure_pos_iff_volume _).mpr
      (volume_meshBall_pos hlam (hrpos 0) center)
  · exact hA
  · intro n
    exact invariantSupport_dichotomy_meshBall_of_closure_subset G
      (meshBall lam R center) (isOpen_meshBall lam R center) A hA hAinv
      hlam (hrpos n) center (closure_meshBall_subset_of_lt (hrlt n) center)

/-- A nonnegative datum whose support is preserved by its own killed orbit
has support either null or conull inside the killing mesh ball. -/
theorem killedL2_support_dichotomy_killing_meshBall_of_self {R : ℝ}
    (hlam : 0 < lam) (hR : 0 < R) (center : Vec d)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, 0 ≤ f x)
    (hself : ∀ t : ℝ≥0, ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      f x = 0 → gmpKilledL2Operator G (meshBall lam R center)
        (isOpen_meshBall lam R center) t f x = 0) :
    (physicalReversibleMeasure ω hd lam).restrict (meshBall lam R center)
        {x | f x ≠ 0} = 0 ∨
      (physicalReversibleMeasure ω hd lam).restrict (meshBall lam R center)
        {x | f x ≠ 0}ᶜ = 0 := by
  let A : Set (Vec d) := {x | f x ≠ 0}
  have hA : MeasurableSet A := by
    exact ((measurableSet_singleton (0 : ℝ)).preimage
      (Lp.stronglyMeasurable f).measurable).compl
  apply invariantSupport_dichotomy_killing_meshBall G hlam hR center A hA
  intro t v hv
  have hv' : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, f x = 0 → v x = 0 := by
    filter_upwards [hv] with x hx hfx
    exact hx (by simp only [A, Set.mem_setOf_eq, not_not]; exact hfx)
  have h := killedL2_support_invariant_of_self G (meshBall lam R center)
    (isOpen_meshBall lam R center) t f hf (hself t) v hv'
  filter_upwards [h] with x hx hxA
  exact hx (by simpa only [A, Set.mem_setOf_eq, not_not] using hxA)

/-- A nonzero nonnegative interior datum with self-invariant support is
strictly positive almost everywhere in the killing mesh ball. -/
theorem killedL2_pos_ae_killing_meshBall_of_self {R : ℝ}
    (hlam : 0 < lam) (hR : 0 < R) (center : Vec d)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hf : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, 0 ≤ f x)
    (hfin : f ∈ physicalZeroBoundaryL2 (meshBall lam R center) hd ω lam L hω)
    (hfne : f ≠ 0)
    (hself : ∀ t : ℝ≥0, ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      f x = 0 → gmpKilledL2Operator G (meshBall lam R center)
        (isOpen_meshBall lam R center) t f x = 0) :
    ∀ᵐ x ∂(physicalReversibleMeasure ω hd lam).restrict (meshBall lam R center),
      0 < f x := by
  let U := meshBall lam R center
  have hU : IsOpen U := isOpen_meshBall lam R center
  have hsplit := killedL2_support_dichotomy_killing_meshBall_of_self G hlam hR center f hf hself
  have hnotnull : (physicalReversibleMeasure ω hd lam).restrict U {x | f x ≠ 0} ≠ 0 := by
    intro hnull
    have hin : ∀ᵐ x ∂(physicalReversibleMeasure ω hd lam).restrict U, f x = 0 := by
      rw [ae_iff]
      exact hnull
    have hin' := (ae_restrict_iff' hU.measurableSet).mp hin
    have hout := (mem_physicalZeroBoundaryL2_iff_zero_off U hU hd ω lam L hω f).mp hfin
    apply hfne
    apply Lp.ext
    filter_upwards [hin', hout, Lp.coeFn_zero ℝ 2 (physicalReversibleMeasure ω hd lam)]
      with x hx hy hz
    by_cases hxU : x ∈ U
    · rw [hx hxU, hz]
      rfl
    · rw [hy hxU, hz]
      rfl
  have hnull := hsplit.resolve_left hnotnull
  have hne : ∀ᵐ x ∂(physicalReversibleMeasure ω hd lam).restrict U, f x ≠ 0 := by
    rw [ae_iff]
    exact hnull
  filter_upwards [hne, ae_restrict_of_ae hf] with x hx hn
  exact lt_of_le_of_ne hn (Ne.symm hx)

/-- Self-invariance of the killed terminal indicator yields the precise
almost-everywhere endpoint positivity needed for mesh-step transport. -/
theorem killedEndpoint_pos_ae_meshBall_of_indicator_self {R : ℝ}
    (hlam : 0 < lam) (hR : 0 < R) (center : Vec d)
    (B : Set (Vec d)) (hB : MeasurableSet B)
    (hBfin : physicalReversibleMeasure ω hd lam B ≠ ∞)
    (hBpos : 0 < physicalReversibleMeasure ω hd lam B)
    (hBU : B ⊆ meshBall lam R center) (t : ℝ≥0)
    (hself : ∀ a : ℝ≥0, ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      gmpKilledL2Operator G (meshBall lam R center) (isOpen_meshBall lam R center) t
          (indicatorConstLp 2 hB hBfin (1 : ℝ)) x = 0 →
      gmpKilledL2Operator G (meshBall lam R center) (isOpen_meshBall lam R center) a
        (gmpKilledL2Operator G (meshBall lam R center) (isOpen_meshBall lam R center) t
          (indicatorConstLp 2 hB hBfin (1 : ℝ))) x = 0) :
    ∀ᵐ x ∂(physicalReversibleMeasure ω hd lam).restrict (meshBall lam R center),
      0 < gmpKilledEndpointKernel G (meshBall lam R center)
        (isOpen_meshBall lam R center) t x B := by
  let U := meshBall lam R center
  let f := indicatorConstLp 2 hB hBfin (1 : ℝ)
  have hrep : f =ᵐ[physicalReversibleMeasure ω hd lam] B.indicator (fun _ => (1 : ℝ)) :=
    indicatorConstLp_coeFn (p := 2) (hs := hB) (hμs := hBfin) (c := (1 : ℝ))
  have hf : f ∈ physicalZeroBoundaryL2 U hd ω lam L hω := by
    apply (mem_physicalZeroBoundaryL2_iff_zero_off U (isOpen_meshBall lam R center)
      hd ω lam L hω f).mpr
    filter_upwards [hrep] with x hx hxU
    rw [hx, Set.indicator_of_notMem (fun hxB => hxU (hBU hxB))]
  have hfn : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, 0 ≤ f x := by
    filter_upwards [hrep] with x hx
    rw [hx]
    by_cases hxB : x ∈ B <;> simp [hxB]
  have hfne : f ≠ 0 := by
    intro hfzero
    have hz : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, f x = 0 := by
      rw [hfzero]
      exact Lp.coeFn_zero ℝ 2 _
    have hempty : ∀ᵐ x ∂(physicalReversibleMeasure ω hd lam).restrict B, False := by
      filter_upwards [ae_restrict_of_ae hrep, ae_restrict_of_ae hz, ae_restrict_mem hB]
        with x hx hz hxB
      rw [hx, Set.indicator_of_mem hxB] at hz
      exact one_ne_zero hz
    have hzero : physicalReversibleMeasure ω hd lam B = 0 := by
      simpa using (ae_iff.mp hempty)
    exact hBpos.ne' hzero
  have hTne : gmpKilledL2Operator G U (isOpen_meshBall lam R center) t f ≠ 0 :=
    fun hz => hfne ((killedL2_eq_zero_iff G U (isOpen_meshBall lam R center) t f hf).mp hz)
  have hpos := killedL2_pos_ae_killing_meshBall_of_self G hlam hR center
    (gmpKilledL2Operator G U (isOpen_meshBall lam R center) t f)
    (killedL2_nonneg G U (isOpen_meshBall lam R center) t f hfn)
    (gmpKilledL2_mem_zeroBoundaryL2 G U (isOpen_meshBall lam R center) t f)
    hTne hself
  filter_upwards [hpos, ae_restrict_of_ae
    (gmpKilledL2_indicatorConst_ae_eq G U (isOpen_meshBall lam R center) t B hB hBfin (1 : ℝ))]
    with x hx houtput
  rw [houtput, mul_one] at hx
  exact ENNReal.toReal_pos_iff.mp hx |>.1

/-- Every nondegenerate terminal mesh ball has positive actual physical
reference mass; both the force and the original potential are retained. -/
theorem physicalReversibleMeasure_meshTerminalBall_pos (i : Fin d)
    {l : ℝ} (hl : 0 < l) (hlam : 0 < lam) (k : ℕ) :
    0 < physicalReversibleMeasure ω hd lam
      (meshBall lam ((l / 32) / 16) (tubeCenters i l (k + 1))) := by
  rw [physicalReversibleMeasure_pos_iff_volume]
  exact volume_meshBall_pos hlam (by positivity) _

/-- Every nondegenerate mesh ball has finite physical reference mass. -/
theorem physicalReversibleMeasure_meshBall_ne_top {R : ℝ}
    (hlam : 0 < lam) (hR : 0 < R) (center : Vec d) :
    physicalReversibleMeasure ω hd lam (meshBall lam R center) ≠ ∞ := by
  letI : IsLocallyFiniteMeasure (physicalReversibleMeasure ω hd lam) :=
    SpatialDirichlet.densityWeightedMeasure_locallyFinite _
      (physicalReversibleDensity_continuous ω hd lam)
  exact ((meshBall_isOpenBoundedConvexDomain hlam hR center).isBoundedDomain.isBounded.measure_lt_top
    (μ := physicalReversibleMeasure ω hd lam)).ne

/-- The invariant-indicator consumer at the original mesh killing domain and
terminal ball, with their positive and finite reference masses discharged. -/
theorem meshTerminalBall_killed_pos_ae_of_indicator_self (i : Fin d)
    {l : ℝ} (hl : 0 < l) (hlam : 0 < lam) (k : ℕ) (t : ℝ≥0)
    (hself : ∀ a : ℝ≥0, ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      gmpKilledL2Operator G (meshBall lam ((l / 32) / 2) (tubeCenters i l k))
          (isOpen_meshBall lam ((l / 32) / 2) (tubeCenters i l k)) t
          (indicatorConstLp 2 (isOpen_meshBall lam ((l / 32) / 16)
            (tubeCenters i l (k + 1))).measurableSet
            (physicalReversibleMeasure_meshBall_ne_top (ω := ω) (hd := hd) hlam
              (by positivity) (tubeCenters i l (k + 1))) (1 : ℝ)) x = 0 →
      gmpKilledL2Operator G (meshBall lam ((l / 32) / 2) (tubeCenters i l k))
          (isOpen_meshBall lam ((l / 32) / 2) (tubeCenters i l k)) a
        (gmpKilledL2Operator G (meshBall lam ((l / 32) / 2) (tubeCenters i l k))
          (isOpen_meshBall lam ((l / 32) / 2) (tubeCenters i l k)) t
          (indicatorConstLp 2 (isOpen_meshBall lam ((l / 32) / 16)
            (tubeCenters i l (k + 1))).measurableSet
            (physicalReversibleMeasure_meshBall_ne_top (ω := ω) (hd := hd) hlam
              (by positivity) (tubeCenters i l (k + 1))) (1 : ℝ))) x = 0) :
    ∀ᵐ x ∂(physicalReversibleMeasure ω hd lam).restrict
        (meshBall lam ((l / 32) / 2) (tubeCenters i l k)),
      0 < gmpKilledEndpointKernel G
        (meshBall lam ((l / 32) / 2) (tubeCenters i l k))
        (isOpen_meshBall lam ((l / 32) / 2) (tubeCenters i l k)) t x
        (meshBall lam ((l / 32) / 16) (tubeCenters i l (k + 1))) := by
  exact killedEndpoint_pos_ae_meshBall_of_indicator_self G hlam (by positivity)
    (tubeCenters i l k) _ (isOpen_meshBall _ _ _).measurableSet
    (physicalReversibleMeasure_meshBall_ne_top hlam (by positivity) _)
    (physicalReversibleMeasure_meshTerminalBall_pos i hl hlam k)
    (meshTerminalBall_subset_domain i hl lam k) t hself

/-- Enlarging an open killing domain increases the actual endpoint measure. -/
theorem killedEndpoint_mono_domain (U V : Set (Vec d)) (hU : IsOpen U)
    (hV : IsOpen V) (hUV : U ⊆ V) (t : ℝ≥0) (x : Vec d) :
    gmpKilledEndpointKernel G U hU t x ≤ gmpKilledEndpointKernel G V hV t x := by
  rw [gmpKilledEndpointKernel_apply, gmpKilledEndpointKernel_apply]
  apply Measure.map_mono _ (measurable_pathPosition t)
  apply Measure.restrict_mono_set
  intro γ hγ
  change (t : ℝ≥0∞) < Diffusion.localityExitTime U γ at hγ
  change (t : ℝ≥0∞) < Diffusion.localityExitTime V γ
  rw [lt_localityExitTime_iff U hU] at hγ
  rw [lt_localityExitTime_iff V hV]
  exact fun s hs => hUV (hγ s hs)

/-- At an interior point of an open target, its actual killed mass is positive
at every sufficiently small time. This local seed does not assert reachability
from other points of the killing domain. -/
theorem killedEndpoint_mass_pos_eventually_at_zero (U B : Set (Vec d))
    (hU : IsOpen U) (hB : IsOpen B) (x : Vec d) (hxU : x ∈ U) (hxB : x ∈ B) :
    ∀ᶠ t : ℝ≥0 in nhds 0, 0 < gmpKilledEndpointKernel G U hU t x B := by
  have hlim := tendsto_integral_gmpKilledEndpointKernel_at_zero G (U ∩ B)
    (hU.inter hB) x ⟨hxU, hxB⟩ (fun _ => (1 : ℝ)) continuous_const 1
    (by intro y; norm_num)
  filter_upwards [hlim.eventually (Ioi_mem_nhds zero_lt_one)] with t ht
  have hmass : 0 < gmpKilledEndpointKernel G (U ∩ B) (hU.inter hB) t x Set.univ := by
    apply bot_lt_iff_ne_bot.mpr
    intro hz
    have hzero := Measure.measure_univ_eq_zero.mp hz
    simp only [hzero, integral_zero_measure, lt_self_iff_false] at ht
  have heq : gmpKilledEndpointKernel G (U ∩ B) (hU.inter hB) t x B =
      gmpKilledEndpointKernel G (U ∩ B) (hU.inter hB) t x Set.univ := by
    apply measure_congr
    filter_upwards [gmpKilledEndpointKernel_ae_mem G (U ∩ B) (hU.inter hB) t x]
      with y hy
    simp only [Set.mem_univ, hy.2]
  exact (heq ▸ hmass).trans_le
    (killedEndpoint_mono_domain G (U ∩ B) U (hU.inter hB) hU Set.inter_subset_left t x B)

/-- The local open-target seed can be taken strictly before any given horizon. -/
theorem exists_pos_lt_killedEndpoint_mass_pos (U B : Set (Vec d))
    (hU : IsOpen U) (hB : IsOpen B) (x : Vec d) (hxU : x ∈ U) (hxB : x ∈ B)
    (t : ℝ≥0) (ht : 0 < t) :
    ∃ s : ℝ≥0, 0 < s ∧ s < t ∧ 0 < gmpKilledEndpointKernel G U hU s x B := by
  obtain ⟨a, ha, hgood⟩ := NNReal.nhds_zero_basis.mem_iff.mp
    (killedEndpoint_mass_pos_eventually_at_zero G U B hU hB x hxU hxB)
  let s := min a t / 2
  have hs : 0 < s := half_pos (lt_min ha ht)
  have hsmall : s < min a t := half_lt_self (lt_min ha ht)
  exact ⟨s, hs, hsmall.trans_le (min_le_right a t),
    hgood (hsmall.trans_le (min_le_left a t))⟩

/-- At each point in the literal terminal mesh ball, the actual killed
transition into that ball is positive for all sufficiently small times. -/
theorem meshTerminalBall_killed_mass_pos_eventually_at_zero (i : Fin d)
    {l : ℝ} (hl : 0 < l) (k : ℕ) (x : Vec d)
    (hx : x ∈ meshBall lam ((l / 32) / 16) (tubeCenters i l (k + 1))) :
    ∀ᶠ t : ℝ≥0 in nhds 0,
      0 < gmpKilledEndpointKernel G
        (meshBall lam ((l / 32) / 2) (tubeCenters i l k))
        (isOpen_meshBall lam ((l / 32) / 2) (tubeCenters i l k)) t x
        (meshBall lam ((l / 32) / 16) (tubeCenters i l (k + 1))) :=
  killedEndpoint_mass_pos_eventually_at_zero G _ _ (isOpen_meshBall _ _ _)
    (isOpen_meshBall _ _ _) x (meshTerminalBall_subset_domain i hl lam k hx) hx

/-- Positive mass reaching a measurable entrance set propagates through any
actual killed continuation positive at physical-almost every point of that set.
The entrance mass remains an explicit reachability obligation. -/
theorem killedEndpoint_mass_pos_of_positive_entrance (U : Set (Vec d)) (hU : IsOpen U)
    (A B : Set (Vec d)) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (s t : ℝ≥0) (hs : 0 < s) (x : Vec d)
    (henter : 0 < gmpKilledEndpointKernel G U hU s x A)
    (hcontinue : ∀ᵐ y ∂(physicalReversibleMeasure ω hd lam).restrict A,
      0 < gmpKilledEndpointKernel G U hU t y B) :
    0 < gmpKilledEndpointKernel G U hU (s + t) x B := by
  have hae := (ae_restrict_iff' hA).mp hcontinue
  have hentrance :=
    (gmpKilledEndpointKernel_absolutelyContinuous_physical G U hU s hs x).ae_le hae
  rw [gmpKilledEndpointKernel_add G U hU s t, Kernel.comp_apply' _ _ _ hB,
    lintegral_pos_iff_support ((gmpKilledEndpointKernel G U hU t).measurable_coe hB)]
  apply henter.trans_le
  apply measure_mono_ae
  filter_upwards [hentrance] with y hy
  intro hyA
  exact (hy hyA).ne'

/-- Almost-everywhere strict positivity of actual killed transitions upgrades
to every interior start. The entrance law is the actual positive-time killed
kernel, whose absolute continuity and short-time survival are already proved. -/
theorem killedEndpoint_mass_pos_of_ae_pos (U : Set (Vec d)) (hU : IsOpen U)
    (B : Set (Vec d)) (hB : MeasurableSet B) (t : ℝ≥0) (ht : 0 < t)
    (hpos : ∀ s : ℝ≥0, 0 < s → s ≤ t →
      ∀ᵐ y ∂(physicalReversibleMeasure ω hd lam).restrict U,
        0 < gmpKilledEndpointKernel G U hU s y B)
    (x : Vec d) (hx : x ∈ U) :
    0 < gmpKilledEndpointKernel G U hU t x B := by
  obtain ⟨s, hs, hst, hmass⟩ := exists_pos_lt_killed_mass_ne_zero G U hU t ht x hx
  have hae := (ae_restrict_iff' hU.measurableSet).mp
    (hpos (t - s) (tsub_pos_iff_lt.mpr hst) tsub_le_self)
  have hentrance := (gmpKilledEndpointKernel_absolutelyContinuous_physical G U hU s hs x).ae_le hae
  have htime : s + (t - s) = t := add_tsub_cancel_of_le hst.le
  rw [← htime, gmpKilledEndpointKernel_add G U hU s (t - s),
    Kernel.comp_apply' _ _ _ hB, lintegral_pos_iff_support
      ((gmpKilledEndpointKernel G U hU (t - s)).measurable_coe hB)]
  apply lt_of_lt_of_le (bot_lt_iff_ne_bot.mpr hmass)
  apply measure_mono_ae
  filter_upwards [hentrance, gmpKilledEndpointKernel_ae_mem G U hU s x] with y hy hyU
  intro _
  exact (hy hyU).ne'

/-- Killed endpoint positivity on an interior domain gives the literal closed
mesh block, including its endpoint restriction. -/
theorem meshPiece_mass_pos_of_killed_ae_pos (ε : ℝ) (τ : ℝ≥0) (hτ : 0 < τ)
    (c : ℕ → Vec d) (k : ℕ) (x : Vec d)
    (hx : x ∈ meshBall lam (ε / 2) (c k))
    (hpos : ∀ s : ℝ≥0, 0 < s → s ≤ τ →
      ∀ᵐ y ∂(physicalReversibleMeasure ω hd lam).restrict (meshBall lam (ε / 2) (c k)),
        0 < gmpKilledEndpointKernel G (meshBall lam (ε / 2) (c k))
          (isOpen_meshBall lam (ε / 2) (c k)) s y
          (meshBall lam (ε / 16) (c (k + 1)))) :
    0 < G.pathLaw x (meshPiece lam ε τ c k) := by
  have h := killedEndpoint_mass_pos_of_ae_pos G
    (meshBall lam (ε / 2) (c k)) (isOpen_meshBall lam (ε / 2) (c k))
    (meshBall lam (ε / 16) (c (k + 1)))
    (isOpen_meshBall lam (ε / 16) (c (k + 1))).measurableSet τ hτ hpos x hx
  rw [gmpKilledEndpointKernel_apply,
    Measure.map_apply (measurable_pathPosition τ)
      (isOpen_meshBall lam (ε / 16) (c (k + 1))).measurableSet,
    Measure.restrict_apply (((isOpen_meshBall lam (ε / 16) (c (k + 1))).measurableSet).preimage
      (measurable_pathPosition τ))] at h
  have heq : pathPosition τ ⁻¹' meshBall lam (ε / 16) (c (k + 1)) ∩
      {γ : Path d | (τ : ℝ≥0∞) < Diffusion.localityExitTime
        (meshBall lam (ε / 2) (c k)) γ} = meshPiece lam ε τ c k := by
    ext γ
    change (euclideanNorm (lam • γ τ - c (k + 1)) < ε / 16 ∧
      (τ : ℝ≥0∞) < Diffusion.localityExitTime (meshBall lam (ε / 2) (c k)) γ) ↔
      (∀ s : ℝ≥0, s ≤ τ → euclideanNorm (lam • γ s - c k) < ε / 2) ∧
        euclideanNorm (lam • γ τ - c (k + 1)) < ε / 16
    rw [lt_localityExitTime_iff _ (isOpen_meshBall lam (ε / 2) (c k)) γ τ]
    exact and_comm
  simpa only [heq] using h

/-- The same endpoint restriction identity holds for any supplied path law.
No process identification or endpoint density is assumed in this transport. -/
theorem meshPiece_mass_eq_restrict_map (μ : Measure (Path d))
    (ε : ℝ) (τ : ℝ≥0) (c : ℕ → Vec d) (k : ℕ) :
    μ (meshPiece lam ε τ c k) =
      ((μ.restrict {γ | (τ : ℝ≥0∞) <
        Diffusion.localityExitTime (meshBall lam (ε / 2) (c k)) γ}).map
        (pathPosition τ)) (meshBall lam (ε / 16) (c (k + 1))) := by
  rw [Measure.map_apply (measurable_pathPosition τ)
      (isOpen_meshBall lam (ε / 16) (c (k + 1))).measurableSet,
    Measure.restrict_apply (((isOpen_meshBall lam (ε / 16) (c (k + 1))).measurableSet).preimage
      (measurable_pathPosition τ))]
  congr 1
  ext γ
  change ((∀ s : ℝ≥0, s ≤ τ → euclideanNorm (lam • γ s - c k) < ε / 2) ∧
    euclideanNorm (lam • γ τ - c (k + 1)) < ε / 16) ↔
    euclideanNorm (lam • γ τ - c (k + 1)) < ε / 16 ∧
      (τ : ℝ≥0∞) < Diffusion.localityExitTime (meshBall lam (ε / 2) (c k)) γ
  rw [lt_localityExitTime_iff _ (isOpen_meshBall lam (ε / 2) (c k)) γ τ]
  exact and_comm

/-- Domination of the actual killed endpoint measure gives a uniform block
bound. The terminal-ball volume is independent of the translated center. -/
theorem meshPiece_mass_lower_of_killed_domination (μ : Measure (Path d))
    (hdim : 0 < d) (hlam : 0 < lam) (ε : ℝ) (τ : ℝ≥0) (c : ℕ → Vec d) (k : ℕ) (a : ℝ≥0∞)
    (hdom : a • (volume : Measure (Vec d)).restrict (meshBall lam (ε / 16) (c (k + 1))) ≤
      (μ.restrict {γ | (τ : ℝ≥0∞) <
        Diffusion.localityExitTime (meshBall lam (ε / 2) (c k)) γ}).map (pathPosition τ)) :
    a * volume (meshBall lam (ε / 16) (0 : Vec d)) ≤ μ (meshPiece lam ε τ c k) := by
  have h := Measure.le_iff'.mp hdom (meshBall lam (ε / 16) (c (k + 1)))
  rw [Measure.coe_smul, Pi.smul_apply, smul_eq_mul, Measure.restrict_apply_self,
    volume_meshBall_eq hdim hlam] at h
  rwa [meshPiece_mass_eq_restrict_map μ ε τ c k]

/-- The mesh recursion is an identity for the actual path law at arbitrary
deterministic mesh times, not a restart assertion for the split coupling. -/
theorem meshPrefix_mass_succ (ε : ℝ) (τ : ℝ≥0) (c : ℕ → Vec d)
    (m : ℕ) (x : Vec d) :
    G.pathLaw x (meshPrefix lam ε τ c (m + 1)) =
      ∫⁻ Y in meshPrefix lam ε τ c m,
        G.pathLaw (Y ((m : ℝ≥0) * τ)) (meshPiece lam ε τ c m) ∂G.pathLaw x := by
  have he := gmpPathLaw_restrict_past_map_shift G ((m : ℝ≥0) * τ)
    (meshPrefix lam ε τ c m) (measurableSet_meshPrefix_past lam ε τ c m)
  have h := congrArg (fun K : Kernel (Vec d) (Path d) =>
    K x (meshPiece lam ε τ c m)) he
  rw [Kernel.map_apply _ (measurable_gmpShiftPath _),
    Measure.map_apply (measurable_gmpShiftPath _) (measurableSet_meshPiece lam ε τ c m),
    Kernel.comp_apply' _ _ _ (measurableSet_meshPiece lam ε τ c m),
    Kernel.map_apply _ (measurable_pathPosition _),
    lintegral_map (G.pathLaw.measurable_coe (measurableSet_meshPiece lam ε τ c m))
      (measurable_pathPosition _)] at h
  change ((G.pathLaw x).restrict (meshPrefix lam ε τ c m))
    ((gmpShiftPath ((m : ℝ≥0) * τ)) ⁻¹' meshPiece lam ε τ c m) =
      ∫⁻ Y in meshPrefix lam ε τ c m,
        G.pathLaw (Y ((m : ℝ≥0) * τ)) (meshPiece lam ε τ c m) ∂G.pathLaw x at h
  rw [Measure.restrict_apply ((measurableSet_meshPiece lam ε τ c m).preimage
    (measurable_gmpShiftPath _)), Set.inter_comm, ← meshPrefix_succ] at h
  exact h

/-- The last block puts the actual mesh endpoint in its next entrance ball. -/
theorem meshPrefix_endpoint_succ (ε : ℝ) (τ : ℝ≥0) (c : ℕ → Vec d)
    (m : ℕ) {Y : Path d} (hY : Y ∈ meshPrefix lam ε τ c (m + 1)) :
    euclideanNorm (lam • Y (((m + 1 : ℕ) : ℝ≥0) * τ) - c (m + 1)) < ε / 16 := by
  have hlast := (hY m (Nat.lt_succ_self m)).2
  simpa only [gmpShiftPath, ContinuousMap.coe_mk, Nat.cast_add, Nat.cast_one,
    add_mul, one_mul] using hlast

/-- A one-step minorization at every permitted entrance point propagates
through the actual restart recursion. The zero step uses starts-at a.e. -/
theorem meshPrefix_mass_step (ε : ℝ) (τ : ℝ≥0) (c : ℕ → Vec d)
    (m : ℕ) (x : Vec d) (hx : euclideanNorm (lam • x - c 0) < ε / 16)
    (η : ℝ≥0∞)
    (hstep : ∀ y : Vec d, euclideanNorm (lam • y - c m) < ε / 16 →
      η ≤ G.pathLaw y (meshPiece lam ε τ c m)) :
    η * G.pathLaw x (meshPrefix lam ε τ c m) ≤
      G.pathLaw x (meshPrefix lam ε τ c (m + 1)) := by
  rw [meshPrefix_mass_succ G, ← setLIntegral_const]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_of_ae (G.pathLaw_starts_at x),
    ae_restrict_mem (measurableSet_meshPrefix lam ε τ c m)] with Y hstart hY
  apply hstep
  cases m with
  | zero =>
    change Y 0 = x at hstart
    simpa only [Nat.cast_zero, zero_mul, hstart] using hx
  | succ m => exact meshPrefix_endpoint_succ ε τ c m hY

/-- Finite product lower bound, retaining the actual closed-block event. -/
theorem meshPrefix_mass_lower (ε : ℝ) (τ : ℝ≥0) (c : ℕ → Vec d)
    (N : ℕ) (x : Vec d) (hx : euclideanNorm (lam • x - c 0) < ε / 16)
    (η : ℝ≥0∞)
    (hstep : ∀ k : ℕ, k < N → ∀ y : Vec d,
      euclideanNorm (lam • y - c k) < ε / 16 →
        η ≤ G.pathLaw y (meshPiece lam ε τ c k)) :
    ∀ m : ℕ, m ≤ N → η ^ m ≤ G.pathLaw x (meshPrefix lam ε τ c m) := by
  let := G.pathLaw_isMarkovKernel
  intro m hm
  induction m with
  | zero => simp only [pow_zero, meshPrefix_zero, measure_univ, le_refl]
  | succ m ih =>
    calc
      η ^ (m + 1) = η * η ^ m := pow_succ' η m
      _ ≤ η * G.pathLaw x (meshPrefix lam ε τ c m) :=
        mul_le_mul' le_rfl (ih (by omega))
      _ ≤ G.pathLaw x (meshPrefix lam ε τ c (m + 1)) :=
        meshPrefix_mass_step G ε τ c m x hx η (hstep m (by omega))

theorem meshPrefix_mass_pos (ε : ℝ) (τ : ℝ≥0) (c : ℕ → Vec d)
    (N : ℕ) (x : Vec d) (hx : euclideanNorm (lam • x - c 0) < ε / 16)
    (η : ℝ≥0∞) (hη : 0 < η)
    (hstep : ∀ k : ℕ, k < N → ∀ y : Vec d,
      euclideanNorm (lam • y - c k) < ε / 16 →
        η ≤ G.pathLaw y (meshPiece lam ε τ c k)) :
    0 < G.pathLaw x (meshPrefix lam ε τ c N) :=
  lt_of_lt_of_le (bot_lt_iff_ne_bot.mpr (pow_ne_zero N (ne_of_gt hη)))
    (meshPrefix_mass_lower G ε τ c N x hx η hstep N le_rfl)


/-- Strict positivity at every entrance suffices for finite chaining. No common
lower bound across entrances or blocks is required. -/
theorem meshPrefix_mass_pos_of_step_pos (ε : ℝ) (τ : ℝ≥0) (c : ℕ → Vec d)
    (N : ℕ) (x : Vec d) (hx : euclideanNorm (lam • x - c 0) < ε / 16)
    (hstep : ∀ k : ℕ, k < N → ∀ y : Vec d,
      euclideanNorm (lam • y - c k) < ε / 16 →
        0 < G.pathLaw y (meshPiece lam ε τ c k)) :
    0 < G.pathLaw x (meshPrefix lam ε τ c N) := by
  let := G.pathLaw_isMarkovKernel
  suffices ∀ m : ℕ, m ≤ N → 0 < G.pathLaw x (meshPrefix lam ε τ c m) from
    this N le_rfl
  intro m hm
  induction m with
  | zero => simp only [meshPrefix_zero, measure_univ, zero_lt_one]
  | succ m ih =>
    rw [meshPrefix_mass_succ G]
    apply (setLIntegral_pos_iff
      ((G.pathLaw.measurable_coe (measurableSet_meshPiece lam ε τ c m)).comp
        (measurable_pathPosition _))).2
    apply lt_of_lt_of_le (ih (by omega))
    apply measure_mono_ae
    filter_upwards [G.pathLaw_starts_at x] with Y hstart
    intro hY
    refine ⟨?_, hY⟩
    change G.pathLaw (Y ((m : ℝ≥0) * τ)) (meshPiece lam ε τ c m) ≠ 0
    apply (hstep m (by omega) _ ?_).ne'
    cases m with
    | zero =>
      change Y 0 = x at hstart
      simpa only [Nat.cast_zero, zero_mul, hstart] using hx
    | succ m => exact meshPrefix_endpoint_succ ε τ c m hY

/-- Pointwise positive closed blocks give the actual literal tube positive mass. -/
theorem tubeEvent_mass_pos_of_step_pos (i : Fin d) (l : ℝ) (hl : 0 < l)
    (hlam : 0 < lam)
    (hstep : ∀ k : ℕ, k < 3200 → ∀ y : Vec d,
      euclideanNorm (lam • y - tubeCenters i l k) < (l / 32) / 16 →
        0 < G.pathLaw y
          (meshPiece lam (l / 32) (tubeStepTime lam) (tubeCenters i l) k)) :
    0 < G.pathLaw 0 (tubeEvent i lam l) :=
  lt_of_lt_of_le (meshPrefix_mass_pos_of_step_pos G (l / 32) (tubeStepTime lam)
    (tubeCenters i l) 3200 0 (tubeCenters_origin_mem i lam hl) hstep)
    (measure_mono (meshPrefix_subset_tubeEvent i hlam hl))

/-- For each fixed block, analytic positivity is needed only at almost every
interior starting point and at positive times up to the block duration. Actual
killed restart supplies every mesh entrance and hence the literal tube. -/
theorem tubeEvent_mass_pos_of_killed_ae_pos (i : Fin d) (l : ℝ) (hl : 0 < l)
    (hlam : 0 < lam)
    (hstep : ∀ k : ℕ, k < 3200 → ∀ s : ℝ≥0, 0 < s → s ≤ tubeStepTime lam →
      ∀ᵐ y ∂(physicalReversibleMeasure ω hd lam).restrict
          (meshBall lam ((l / 32) / 2) (tubeCenters i l k)),
        0 < gmpKilledEndpointKernel G
          (meshBall lam ((l / 32) / 2) (tubeCenters i l k))
          (isOpen_meshBall lam ((l / 32) / 2) (tubeCenters i l k)) s y
          (meshBall lam ((l / 32) / 16) (tubeCenters i l (k + 1)))) :
    0 < G.pathLaw 0 (tubeEvent i lam l) := by
  apply tubeEvent_mass_pos_of_step_pos G i l hl hlam
  intro k hk y hy
  apply meshPiece_mass_pos_of_killed_ae_pos G (l / 32) (tubeStepTime lam)
    (tubeStepTime_pos hlam) (tubeCenters i l) k y ?_ (hstep k hk)
  change euclideanNorm (lam • y - tubeCenters i l k) < (l / 32) / 2
  linarith only [hy, hl]

/-- Invariance of each positive-time terminal-indicator orbit yields positive
mass of the literal tube for this fixed-environment realization. -/
theorem tubeEvent_mass_pos_of_mesh_indicator_self (i : Fin d) (l : ℝ)
    (hl : 0 < l) (hlam : 0 < lam)
    (hself : ∀ k : ℕ, k < 3200 → ∀ t : ℝ≥0, 0 < t →
      t ≤ tubeStepTime lam → ∀ a : ℝ≥0, ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      gmpKilledL2Operator G (meshBall lam ((l / 32) / 2) (tubeCenters i l k))
          (isOpen_meshBall lam ((l / 32) / 2) (tubeCenters i l k)) t
          (indicatorConstLp 2 (isOpen_meshBall lam ((l / 32) / 16)
            (tubeCenters i l (k + 1))).measurableSet
            (physicalReversibleMeasure_meshBall_ne_top (ω := ω) (hd := hd) hlam
              (by positivity) (tubeCenters i l (k + 1))) (1 : ℝ)) x = 0 →
      gmpKilledL2Operator G (meshBall lam ((l / 32) / 2) (tubeCenters i l k))
          (isOpen_meshBall lam ((l / 32) / 2) (tubeCenters i l k)) a
        (gmpKilledL2Operator G (meshBall lam ((l / 32) / 2) (tubeCenters i l k))
          (isOpen_meshBall lam ((l / 32) / 2) (tubeCenters i l k)) t
          (indicatorConstLp 2 (isOpen_meshBall lam ((l / 32) / 16)
            (tubeCenters i l (k + 1))).measurableSet
            (physicalReversibleMeasure_meshBall_ne_top (ω := ω) (hd := hd) hlam
              (by positivity) (tubeCenters i l (k + 1))) (1 : ℝ))) x = 0) :
    0 < G.pathLaw 0 (tubeEvent i lam l) := by
  apply tubeEvent_mass_pos_of_killed_ae_pos G i l hl hlam
  intro k hk t ht htime
  exact meshTerminalBall_killed_pos_ae_of_indicator_self G i hl hlam k t
    (hself k hk t ht htime)

/-- The genuine closed-block product bound gives the literal first tube positive
mass. The displayed inequalities are ordinary one-block estimates for this law. -/
theorem tubeEvent_mass_lower (i : Fin d) (l : ℝ) (hl : 0 < l) (hlam : 0 < lam)
    (η : ℝ≥0∞)
    (hstep : ∀ k : ℕ, k < 3200 → ∀ y : Vec d,
      euclideanNorm (lam • y - tubeCenters i l k) < (l / 32) / 16 →
        η ≤ G.pathLaw y
          (meshPiece lam (l / 32) (tubeStepTime lam) (tubeCenters i l) k)) :
    η ^ 3200 ≤ G.pathLaw 0 (tubeEvent i lam l) :=
  le_trans (meshPrefix_mass_lower G (l / 32) (tubeStepTime lam) (tubeCenters i l)
    3200 0 (tubeCenters_origin_mem i lam hl) η hstep 3200 le_rfl)
    (measure_mono (meshPrefix_subset_tubeEvent i hlam hl))

/-- Explicit transport from the all-start GMP realization to the actual reduced
kernel. No process realization or step estimate is inserted as an axiom. -/
theorem ae_quenched_tubeEvent_mass_lower {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (hlam : 0 < lam)
    (P : QuenchedPathLaws d) (hGMP : IsGMPReducedKernel hd hΛ₀ Q lam h0 h1 P)
    (i : Fin d) (l : ℝ) (hl : 0 < l) (η : ℝ≥0∞)
    (hstep : ∀ᵐ ω ∂Q.measure, ∀ k : ℕ, k < 3200 → ∀ y : Vec d,
      euclideanNorm (lam • y - tubeCenters i l k) < (l / 32) / 16 →
        η ≤ P (y, ω)
          (meshPiece lam (l / 32) (tubeStepTime lam) (tubeCenters i l) k)) :
    ∀ᵐ ω ∂Q.measure, η ^ 3200 ≤ P (0, ω) (tubeEvent i lam l) := by
  filter_upwards [hGMP, hstep] with ω hω hstepω
  obtain ⟨hreg, Gω, hGω⟩ := hω
  rw [hGω 0]
  apply tubeEvent_mass_lower Gω i l hl hlam η
  intro k hk y hy
  simpa only [hGω y] using hstepω k hk y hy

/-- The qualitative chaining estimate transports to the original quenched
kernel with its original almost-everywhere environment qualifier. -/
theorem ae_quenched_tubeEvent_mass_pos_of_step_pos {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (hlam : 0 < lam)
    (P : QuenchedPathLaws d) (hGMP : IsGMPReducedKernel hd hΛ₀ Q lam h0 h1 P)
    (i : Fin d) (l : ℝ) (hl : 0 < l)
    (hstep : ∀ᵐ ω ∂Q.measure, ∀ k : ℕ, k < 3200 → ∀ y : Vec d,
      euclideanNorm (lam • y - tubeCenters i l k) < (l / 32) / 16 →
        0 < P (y, ω)
          (meshPiece lam (l / 32) (tubeStepTime lam) (tubeCenters i l) k)) :
    ∀ᵐ ω ∂Q.measure, 0 < P (0, ω) (tubeEvent i lam l) := by
  filter_upwards [hGMP, hstep] with ω hω hstepω
  obtain ⟨hreg, Gω, hGω⟩ := hω
  rw [hGω 0]
  apply tubeEvent_mass_pos_of_step_pos Gω i l hl hlam
  intro k hk y hy
  simpa only [hGω y] using hstepω k hk y hy

/-- The physical-a.e. qualitative killed estimate for the supplied actual
path laws gives positive tube mass on a single environment-conull set. This
consumer retains every mesh index and needs no uniform positive lower bound. -/
theorem ae_quenched_tubeEvent_mass_pos_of_killed_ae_pos {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (hlam : 0 < lam)
    (P : QuenchedPathLaws d) (hGMP : IsGMPReducedKernel hd hΛ₀ Q lam h0 h1 P)
    (i : Fin d) (l : ℝ) (hl : 0 < l)
    (hstep : ∀ᵐ ω ∂Q.measure, ∀ k : ℕ, k < 3200 →
      ∀ s : ℝ≥0, 0 < s → s ≤ tubeStepTime lam →
      ∀ᵐ y ∂(physicalReversibleMeasure ω hd lam).restrict
          (meshBall lam ((l / 32) / 2) (tubeCenters i l k)),
        0 < Measure.map (pathPosition s)
          ((P (y, ω)).restrict {γ : Path d | (s : ℝ≥0∞) < Diffusion.localityExitTime
            (meshBall lam ((l / 32) / 2) (tubeCenters i l k)) γ})
          (meshBall lam ((l / 32) / 16) (tubeCenters i l (k + 1)))) :
    ∀ᵐ ω ∂Q.measure, 0 < P (0, ω) (tubeEvent i lam l) := by
  filter_upwards [hGMP, hstep] with ω hω hstepω
  obtain ⟨hreg, Gω, hGω⟩ := hω
  rw [hGω 0]
  apply tubeEvent_mass_pos_of_killed_ae_pos Gω i l hl hlam
  intro k hk s hs hst
  apply (physicalReversibleMeasure_restrict_ae_iff_volume _
    (isOpen_meshBall _ _ _).measurableSet _).mpr
  have hvol := (physicalReversibleMeasure_restrict_ae_iff_volume _
    (isOpen_meshBall _ _ _).measurableSet _).mp (hstepω k hk s hs hst)
  filter_upwards [hvol] with y hy
  rw [gmpKilledEndpointKernel_apply, ← hGω y]
  exact hy

/-- Positive quenched tube probabilities give positive actual annealed mass,
even without a common lower bound over the environments. -/
theorem annealed_tubeEvent_mass_pos {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (K : Regeneration.CoupledQuenchedLaws d)
    (P : QuenchedPathLaws d) (hprob : Regeneration.HasProbabilityLaws Q K)
    (hmarg : Regeneration.HasPathMarginals Q K P) (i : Fin d) (lam l : ℝ)
    (hpath : ∀ᵐ ω ∂Q, 0 < P (0, ω) (tubeEvent i lam l)) :
    0 < Regeneration.annealedCoupledLaw Q K {q | q.2.1 ∈ tubeEvent i lam l} := by
  rw [Regeneration.annealedCoupledLaw, Measure.compProd_apply
    (show MeasurableSet {q : FieldPair d × Regeneration.CoupledSample d |
      q.2.1 ∈ tubeEvent i lam l} from
        (measurableSet_tubeEvent i lam l).preimage measurable_snd.fst)]
  change 0 < ∫⁻ ω, Probability.probabilityPart (Regeneration.originCoupledLaw K) ω
    (Prod.fst ⁻¹' tubeEvent i lam l) ∂Q
  apply bot_lt_iff_ne_bot.mpr
  intro hzero
  have hz := (lintegral_eq_zero_iff
    ((Probability.probabilityPart (Regeneration.originCoupledLaw K)).measurable_coe
      ((measurableSet_tubeEvent i lam l).preimage measurable_fst))).mp hzero
  have hfalse : ∀ᵐ ω ∂Q, False := by
    filter_upwards [hprob.1, hmarg.1, hpath, hz] with ω hp hm hpos hzeroω
    have : IsProbabilityMeasure (Regeneration.originCoupledLaw K ω) := hp
    rw [Probability.probabilityPart_eq_of_isProbabilityMeasure] at hzeroω
    change K (0, ω) (Prod.fst ⁻¹' tubeEvent i lam l) = 0 at hzeroω
    rw [← Measure.map_apply measurable_fst (measurableSet_tubeEvent i lam l), hm]
      at hzeroω
    exact hpos.ne' hzeroω
  exact hfalse.exists.choose_spec

/-- Actual annealed tube mass from its quenched path marginal. The probability
part only changes exceptional fibres and is eliminated a.e., rather than
postulating that every coupled fibre is a probability law. -/
theorem annealed_tubeEvent_mass_lower {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (K : Regeneration.CoupledQuenchedLaws d)
    (P : QuenchedPathLaws d) (hprob : Regeneration.HasProbabilityLaws Q K)
    (hmarg : Regeneration.HasPathMarginals Q K P) (i : Fin d) (lam l : ℝ)
    (a : ℝ≥0∞) (hpath : ∀ᵐ ω ∂Q, a ≤ P (0, ω) (tubeEvent i lam l)) :
    a ≤ Regeneration.annealedCoupledLaw Q K {q | q.2.1 ∈ tubeEvent i lam l} := by
  rw [Regeneration.annealedCoupledLaw, Measure.compProd_apply
    (show MeasurableSet {q : FieldPair d × Regeneration.CoupledSample d |
      q.2.1 ∈ tubeEvent i lam l} from
        (measurableSet_tubeEvent i lam l).preimage measurable_snd.fst)]
  calc
    a = ∫⁻ _ω : FieldPair d, a ∂Q := by simp
    _ ≤ _ := by
      apply lintegral_mono_ae
      filter_upwards [hprob.1, hmarg.1, hpath] with ω hp hm hpathω
      have : IsProbabilityMeasure (Regeneration.originCoupledLaw K ω) := hp
      rw [Probability.probabilityPart_eq_of_isProbabilityMeasure]
      change a ≤ K (0, ω) (Prod.fst ⁻¹' tubeEvent i lam l)
      rw [← Measure.map_apply measurable_fst (measurableSet_tubeEvent i lam l), hm]
      exact hpathω

/-- Fresh bit one is independent of the entire first tube history. This is the
actual joint mass identity, so no conditional independence of a future
no-return event is being assumed here. -/
theorem annealed_tubeEvent_fresh_bit_mass {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (K : Regeneration.CoupledQuenchedLaws d)
    (hprob : Regeneration.HasProbabilityLaws Q K) (i : Fin d) (lam l δ : ℝ)
    (hδ : 0 ≤ δ)
    (hfresh : Regeneration.HasFreshBits Q (Regeneration.Renewal.regenDelta lam) δ K) :
    Regeneration.annealedCoupledLaw Q K
      {q | q.2.1 ∈ tubeEvent i lam l ∧ q.2.2 1 = true} =
      ENNReal.ofReal δ * Regeneration.annealedCoupledLaw Q K
        {q | q.2.1 ∈ tubeEvent i lam l} :=
  Regeneration.measure_annealed_fresh_bit Q K hprob _ δ hδ hfresh 1
    {z | z.1 ∈ tubeEvent i lam l} (measurableSet_tubeEvent_history i lam l)

/-- A positive quenched lower bound remains positive after the fresh bit. -/
theorem annealed_tubeEvent_fresh_bit_pos {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (K : Regeneration.CoupledQuenchedLaws d)
    (P : QuenchedPathLaws d) (hprob : Regeneration.HasProbabilityLaws Q K)
    (hmarg : Regeneration.HasPathMarginals Q K P) (i : Fin d) (lam l δ : ℝ)
    (hδ : 0 < δ)
    (hfresh : Regeneration.HasFreshBits Q (Regeneration.Renewal.regenDelta lam) δ K)
    (a : ℝ≥0∞) (ha : 0 < a)
    (hpath : ∀ᵐ ω ∂Q, a ≤ P (0, ω) (tubeEvent i lam l)) :
    0 < Regeneration.annealedCoupledLaw Q K
      {q | q.2.1 ∈ tubeEvent i lam l ∧ q.2.2 1 = true} := by
  rw [annealed_tubeEvent_fresh_bit_mass Q K hprob i lam l δ hδ.le hfresh]
  exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hδ).ne'
    (lt_of_lt_of_le ha (annealed_tubeEvent_mass_lower Q K P hprob hmarg i lam l a hpath)).ne'


/-- The first literal tube already chooses the first candidate at Δ. Forcing
bit one therefore makes its first trial start exactly at 2Δ, for every bit path. -/
theorem tubeEvent_mem_forcedBitTrialEvent {d : ℕ} (hd : 2 ≤ d)
    {lam l : ℝ} (hlam : 0 < lam) (hlam1 : lam ≤ 1) (hl : 0 < l)
    (z : Regeneration.CoupledSample d) (hz0 : z.1 0 = 0)
    (hz : z.1 ∈ tubeEvent (Regeneration.Renewal.forceCoord hd) lam l) :
    z ∈ Regeneration.forcedBitTrialEvent (Regeneration.Renewal.regenDelta lam)
      lam (l / lam) (Regeneration.Renewal.forceCoord hd) 1 := by
  classical
  let Δ := Regeneration.Renewal.regenDelta lam
  let R := l / lam
  let i := Regeneration.Renewal.forceCoord hd
  let z' := Regeneration.forceSampleBit 1 z
  have hΔ : 0 < Δ := Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos hlam))
  have hR : 0 < R := div_pos hl hlam
  have hgeo := node_rt_u3A_renewal_u23_tube_u2D_geometry_of_deps d hd l hl
    lam hlam hlam1 2 (Or.inl rfl) z.1 hz0 (by
      intro u hu
      have hu' : (u : ℝ) ≤ 1 := by norm_num at hu; exact hu
      simpa only [tubeCurve, ite_true] using hz u hu')
  have hround : Regeneration.roundedCandidateSequence Δ lam R (3 * lam * R) z' i 0 =
      (Δ : ℝ≥0∞) := by
    change Regeneration.firstRoundedCandidate Δ lam R (3 * lam * R) z.1 i = _
    simpa only [Nat.reduceSub, Nat.cast_one, one_mul] using hgeo.2.2.2.1
  have hs : Regeneration.IsSuccessfulCandidate Δ lam R (3 * lam * R) z' i 0 := by
    constructor
    · rw [hround]
      exact ENNReal.coe_ne_top
    · rw [hround, ENNReal.toNNReal_coe]
      have hgrid : Regeneration.gridIndex Δ Δ = 1 := by
        simpa only [Nat.cast_one, one_mul] using Regeneration.gridIndex_mul Δ hΔ 1
      simp only [hgrid, z', Regeneration.forceSampleBit, Function.update_self]
  have hupper : Regeneration.firstSuccessfulCandidate Δ lam R (3 * lam * R) z' i ≤
      (Δ : ℝ≥0∞) := by
    rw [Regeneration.firstSuccessfulCandidate]
    refine iInf_le_of_le 0 ?_
    exact iInf_le_of_le hs hround.le
  have hlower := Regeneration.step_le_firstSuccessfulCandidate Δ hΔ lam R
    (3 * lam * R) hlam hR (div_pos (by positivity) hlam) z' i
  have heq := le_antisymm hupper hlower
  refine ⟨0, ?_⟩
  change Regeneration.firstSuccessfulCandidate Δ lam R (3 * lam * R) z' i + Δ = _
  rw [heq]
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat, ENNReal.coe_mul]
  exact (two_mul _).symm


end GMPBounds

/-- One common exceptional environment set suffices for all mesh indices and
all entrance points. Domination concerns the supplied actual path law. -/
theorem ae_meshPiece_mass_lower_of_killed_domination {d : ℕ} (hd : 0 < d)
    (Q : Measure (FieldPair d)) (P : QuenchedPathLaws d) {lam : ℝ} (hlam : 0 < lam)
    (ε : ℝ) (τ : ℝ≥0) (c : ℕ → Vec d) (N : ℕ) (a : ℝ≥0∞)
    (hdom : ∀ᵐ ω ∂Q, ∀ k : ℕ, k < N → ∀ y : Vec d,
      euclideanNorm (lam • y - c k) < ε / 16 →
      a • (volume : Measure (Vec d)).restrict (meshBall lam (ε / 16) (c (k + 1))) ≤
        ((P (y, ω)).restrict {γ | (τ : ℝ≥0∞) <
          Diffusion.localityExitTime (meshBall lam (ε / 2) (c k)) γ}).map (pathPosition τ)) :
    ∀ᵐ ω ∂Q, ∀ k : ℕ, k < N → ∀ y : Vec d,
      euclideanNorm (lam • y - c k) < ε / 16 →
      a * volume (meshBall lam (ε / 16) (0 : Vec d)) ≤
        P (y, ω) (meshPiece lam ε τ c k) := by
  filter_upwards [hdom] with ω hω
  intro k hk y hy
  exact meshPiece_mass_lower_of_killed_domination (P (y, ω)) hd hlam ε τ c k a
    (hω k hk y hy)

/-- A dominated actual killed endpoint law gives the quantitative tube bound
at the literal 3200-block mesh, with unchanged entrance and environment quantifiers. -/
theorem ae_quenched_tubeEvent_mass_lower_of_killed_domination {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (hlam : 0 < lam)
    (P : QuenchedPathLaws d) (hGMP : IsGMPReducedKernel hd hΛ₀ Q lam h0 h1 P)
    (i : Fin d) (l : ℝ) (hl : 0 < l) (a : ℝ≥0∞)
    (hdom : ∀ᵐ ω ∂Q.measure, ∀ k : ℕ, k < 3200 → ∀ y : Vec d,
      euclideanNorm (lam • y - tubeCenters i l k) < (l / 32) / 16 →
      a • (volume : Measure (Vec d)).restrict
          (meshBall lam ((l / 32) / 16) (tubeCenters i l (k + 1))) ≤
        ((P (y, ω)).restrict {γ | (tubeStepTime lam : ℝ≥0∞) <
          Diffusion.localityExitTime
            (meshBall lam ((l / 32) / 2) (tubeCenters i l k)) γ}).map
          (pathPosition (tubeStepTime lam))) :
    ∀ᵐ ω ∂Q.measure,
      (a * volume (meshBall lam ((l / 32) / 16) (0 : Vec d))) ^ 3200 ≤
        P (0, ω) (tubeEvent i lam l) := by
  apply ae_quenched_tubeEvent_mass_lower hd hΛ₀ Q lam h0 h1 hlam P hGMP i l hl
  exact ae_meshPiece_mass_lower_of_killed_domination (by omega) Q.measure P hlam
    (l / 32) (tubeStepTime lam) (tubeCenters i l) 3200 a hdom

section EndpointMass
open Regeneration

/-- The first tube endpoint lies strictly below the successful endpoint ball. -/
theorem tubeEvent_endpoint_coord_lt_four {d : ℕ} (i : Fin d) {lam l : ℝ}
    (hlam : 0 < lam) (hl : 0 < l) {Y : Path d} (hY : Y ∈ tubeEvent i lam l) :
    Y (Renewal.regenDelta lam) i < 4 * (l / lam) := by
  have ht := hY 1 (by norm_num)
  have hm : min (25 * l / 4) (25 * l / 8) = 25 * l / 8 :=
    min_eq_right (by linarith)
  have hn : euclideanNorm (lam • Y (Renewal.regenDelta lam) -
      (25 * l / 8) • unitVector i) < l / 32 := by
    simpa only [tubeCurve, NNReal.coe_one, mul_one, hm, one_div, Renewal.regenDelta] using ht
  have hc := (coordinate_abs_le_euclideanNorm
    (lam • Y (Renewal.regenDelta lam) - (25 * l / 8) • unitVector i) i).trans_lt hn
  have hc' : |lam * Y (Renewal.regenDelta lam) i - 25 * l / 8| < l / 32 := by
    simpa [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, unitVector] using hc
  rw [← mul_div_assoc, lt_div_iff₀ hlam]
  nlinarith only [(abs_lt.mp hc').2, hl]

/-- The actual uniform successful endpoint assigns zero mass to the low
half-space containing the first tube endpoint. -/
theorem endpointAverage_low_eq_zero {d : ℕ} (i : Fin d) (R : ℝ) (hR : 0 < R) :
    endpointAverage i R (0 : Vec d)
      (({y : Vec d | y i < 4 * R}).indicator (fun _ => (1 : ℝ))) = 0 := by
  have hball : MeasurableSet (endpointBall i R (0 : Vec d)) :=
    measurableSet_lt (continuous_euclideanNorm.comp
      (continuous_id.sub continuous_const)).measurable measurable_const
  have hz : (∫ y in endpointBall i R (0 : Vec d),
      ({y : Vec d | y i < 4 * R}).indicator (fun _ => (1 : ℝ)) y) = 0 := by
    calc
      _ = ∫ _ in endpointBall i R (0 : Vec d), (0 : ℝ) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hball] with y hy
        have hc := (coordinate_abs_le_euclideanNorm
          (y - ((0 : Vec d) + (9 * R) • unitVector i)) i).trans_lt hy
        have hc' : |y i - 9 * R| < R := by
          simpa [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, unitVector] using hc
        have hlow : y ∉ {y : Vec d | y i < 4 * R} := by
          change ¬y i < 4 * R
          linarith only [(abs_lt.mp hc').1, hR]
        exact Set.indicator_of_notMem hlow _
      _ = 0 := integral_zero _ _
  simp only [endpointAverage, hz, zero_div]

/-- The integral-form successful endpoint law implies its actual low-endpoint
null event, using the origin law rather than a deterministic-time density. -/
theorem uniformSuccessfulEndpoint_zero_low_null {d : ℕ} (K : CoupledQuenchedLaws d)
    (ω : FieldPair d) (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d) (hR : 0 < R)
    [IsProbabilityMeasure (K (0, ω))]
    (hu : UniformSuccessfulEndpointAt Δ δ R i K (0, ω))
    (hstart : ∀ᵐ z ∂K (0, ω), z.1 0 = 0) :
    ∀ᵐ z ∂K (0, ω), z.2 0 = true → 4 * R ≤ z.1 Δ i := by
  let L : Set (Vec d) := {y | y i < 4 * R}
  let φ : Vec d → ℝ := L.indicator (fun _ => (1 : ℝ))
  have hL : MeasurableSet L := measurableSet_lt (measurable_pi_apply i) measurable_const
  have hφ : Measurable φ := measurable_const.indicator hL
  have hbφ : BoundedRealTest φ := by
    refine ⟨1, fun y => ?_⟩
    by_cases hy : y ∈ L <;> simp [φ, hy]
  let E : Set (CoupledSample d) := {z | z.2 0 = true ∧ z.1 Δ ∈ L}
  have hbit : Measurable (fun z : CoupledSample d => z.2 0) :=
    (measurable_pi_apply (X := fun _ : ℕ => Bool) 0).comp measurable_snd
  have hE : MeasurableSet E :=
    (hbit (measurableSet_singleton true)).inter
      (hL.preimage ((continuous_eval_const Δ).measurable.comp measurable_fst))
  have hu0 := hu 0 (fun _ => (1 : ℝ)) φ measurable_const ⟨1, by simp⟩ hφ hbφ
  simp only [Nat.cast_zero, zero_mul, Nat.zero_add, Nat.cast_one, one_mul] at hu0
  have hz : (∫ z, endpointAverage i R (z.1 0) φ ∂K (0, ω)) = 0 := by
    calc
      _ = ∫ _ : CoupledSample d, (0 : ℝ) ∂K (0, ω) := by
        apply integral_congr_ae
        filter_upwards [hstart] with z hz
        rw [hz]
        exact endpointAverage_low_eq_zero i R hR
      _ = 0 := integral_zero _ _
  rw [hz, mul_zero] at hu0
  have hpt (z : CoupledSample d) :
      (if z.2 0 = true then (1 : ℝ) else 0) * φ (z.1 Δ) =
        E.indicator (fun _ => (1 : ℝ)) z := by
    by_cases hb : z.2 0 = true <;> by_cases hl : z.1 Δ ∈ L <;> simp [φ, E, hb, hl]
  simp_rw [hpt] at hu0
  have hnonneg : 0 ≤ E.indicator (fun _ => (1 : ℝ)) := by
    intro z
    by_cases hz : z ∈ E <;> simp [hz]
  have hzero := (integral_eq_zero_iff_of_nonneg hnonneg
    ((integrable_const (1 : ℝ)).indicator hE)).mp hu0
  filter_upwards [hzero] with z hz
  intro hb
  by_contra hle
  have hmem : z ∈ E := ⟨hb, lt_of_not_ge hle⟩
  simp only [Set.indicator_of_mem hmem, Pi.zero_apply, one_ne_zero] at hz

/-- The successful endpoint law averages the constant one to one. -/
theorem endpointAverage_one {d : ℕ} (i : Fin d) (R : ℝ) (hR : 0 < R)
    (x : Vec d) : endpointAverage i R x (fun _ => (1 : ℝ)) = 1 := by
  have hV : (volume (endpointBall i R x)).toReal ≠ 0 :=
    (ENNReal.toReal_pos (endpointBall_volume_pos i R hR x).ne'
      (endpointBall_volume_ne_top i R hR x)).ne'
  simp only [endpointAverage, integral_const, smul_eq_mul, mul_one,
    measureReal_def, Measure.restrict_apply_univ, div_self hV]

/-- Integrating the literal spatial past kernel recovers the forced trial
expectation with the same endpoint-ball normalization. -/
theorem spatial_past_mass_eq {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (K : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q K) (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R : ℝ) (hR : 0 < R) (i : Fin d) (m : ℕ)
    (H : CoupledSample d → ℝ) (hH : Measurable[finiteHistorySigma Δ m] H)
    (hbH : BoundedRealTest H) :
    (volume (endpointBall i R (0 : Vec d))).toReal⁻¹ *
        (∫ y, ∫ ω, firstSlicePastIntegral Δ lam R i m K H (y, ω) ∂Q) =
      ∫ q, ((forcedBitTrialEvent Δ lam R i m).indicator H) q.2
        ∂annealedCoupledLaw Q K := by
  let G := (forcedBitTrialEvent Δ lam R i m).indicator H
  have hG : Measurable G :=
    (hH.indicator (measurableSet_forcedBitTrialEvent_finiteHistory
      Δ hΔ lam R hR i m)).mono (Probability.finiteHistorySigma_le Δ m) le_rfl
  have hbG : BoundedRealTest G := by
    obtain ⟨C, hC⟩ := hbH
    refine ⟨max C 0, fun z => ?_⟩
    by_cases hz : z ∈ forcedBitTrialEvent Δ lam R i m
    · simpa only [G, Set.indicator_of_mem hz] using (hC z).trans (le_max_left C 0)
    · simpa only [G, Set.indicator_of_notMem hz, abs_zero] using (le_max_right C 0)
  have hf := integral_annealed_endpointAverage_fubini Q K hK Δ m i R hR G hG hbG
    (fun _ => (1 : ℝ)) measurable_const ⟨1, by simp⟩
  simp only [endpointAverage_one i R hR, mul_one] at hf
  have hd := integral_annealedCoupledLaw Q K hK (fun q => G q.2)
    (hG.comp measurable_snd) (by obtain ⟨C, hC⟩ := hbG; exact ⟨C, fun q => hC _⟩)
  exact hf.symm.trans hd.symm

variable (hindep : node_app_u3A_factorization_u23_independenceStmtV2)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
    (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ : 0 < δ) (hδ₁ : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)

include h₀ h₁ hl hK in
/-- On the first tube, bit zero is false almost surely. This follows from
the actual successful endpoint law and its incompatible endpoint geometry. -/
theorem tubeEvent_bit_zero_false_ae :
    ∀ᵐ q ∂annealedCoupledLaw Q.measure K,
      q.2.1 ∈ tubeEvent (Renewal.forceCoord hd) lam l → q.2.2 0 = false := by
  have hbit : Measurable (fun q : FieldPair d × CoupledSample d => q.2.2 0) :=
    (measurable_pi_apply (X := fun _ : ℕ => Bool) 0).comp measurable_snd.snd
  have hmeas : MeasurableSet {q : FieldPair d × CoupledSample d |
      q.2.1 ∈ tubeEvent (Renewal.forceCoord hd) lam l → q.2.2 0 = false} := by
    have he : {q : FieldPair d × CoupledSample d |
        q.2.1 ∈ tubeEvent (Renewal.forceCoord hd) lam l → q.2.2 0 = false} =
        {q | q.2.1 ∈ tubeEvent (Renewal.forceCoord hd) lam l}ᶜ ∪ {q | q.2.2 0 = false} := by
      ext q
      simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_compl_iff, imp_iff_not_or]
    rw [he]
    exact ((measurableSet_tubeEvent (Renewal.forceCoord hd) lam l).preimage
      measurable_snd.fst).compl.union (hbit (measurableSet_singleton false))
  apply Measure.ae_compProd_of_ae_ae hmeas
  filter_upwards [hK.1.1, hK.2.1.1, hK.2.2.1, hK.2.2.2.2.2.2.1.1]
    with ω hp hm hω hu
  have : IsProbabilityMeasure (originCoupledLaw K ω) := hp
  rw [Probability.probabilityPart_eq_of_isProbabilityMeasure (originCoupledLaw K) ω]
  obtain ⟨_, Gω, hGω⟩ := hω
  have hstarts : ∀ᵐ Y ∂P (0, ω), Y 0 = 0 := by
    rw [hGω 0]
    exact Gω.pathLaw_starts_at 0
  rw [← hm] at hstarts
  have hcoupled := ae_of_ae_map measurable_fst.aemeasurable hstarts
  have : IsProbabilityMeasure (K (0, ω)) := hp
  have hh := uniformSuccessfulEndpoint_zero_low_null K ω (Renewal.regenDelta lam)
    δ (l / lam) (Renewal.forceCoord hd) (div_pos hl h₀) hu hcoupled
  filter_upwards [hh] with z hz
  intro ht
  cases hb : z.2 0 with
  | false => rfl
  | true => exact (not_le_of_gt (tubeEvent_endpoint_coord_lt_four
      (Renewal.forceCoord hd) h₀ hl ht) (hz hb)).elim

include hK hδ in
/-- The initial false-bit mass is the actual complementary Bernoulli mass. -/
theorem bit_zero_false_mass :
    annealedCoupledLaw Q.measure K {q | q.2.2 0 = false} = ENNReal.ofReal (1 - δ) := by
  let μ := annealedCoupledLaw Q.measure K
  have : IsProbabilityMeasure μ := annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have ht := measure_annealed_fresh_bit Q.measure K hK.1 (Renewal.regenDelta lam)
    δ hδ.le hK.2.2.2.1 0 Set.univ MeasurableSet.univ
  simp only [Set.mem_univ, true_and, Set.ofPred_true, measure_univ, mul_one] at ht
  have hbit : Measurable (fun q : FieldPair d × CoupledSample d => q.2.2 0) :=
    (measurable_pi_apply (X := fun _ : ℕ => Bool) 0).comp measurable_snd.snd
  have htrue : MeasurableSet {q : FieldPair d × CoupledSample d | q.2.2 0 = true} :=
    measurableSet_eq_fun hbit measurable_const
  have he : {q : FieldPair d × CoupledSample d | q.2.2 0 = false} =
      {q | q.2.2 0 = true}ᶜ := by
    ext q
    cases hb : q.2.2 0 <;> simp [hb]
  change μ {q | q.2.2 0 = false} = _
  rw [he, measure_compl htrue (measure_ne_top μ _),
    measure_univ, ht]
  simpa only [ENNReal.ofReal_one] using (ENNReal.ofReal_sub 1 hδ.le).symm

include h₀ h₁ hl hK hδ in
/-- The tube lies in the initial false-bit event, so its ordinary mass
contains `1 - δ` times its actual false-bit-conditioned mass. -/
theorem tubeEvent_mass_eq_false_zero_cond :
    annealedCoupledLaw Q.measure K {q | q.2.1 ∈ tubeEvent (Renewal.forceCoord hd) lam l} =
      ENNReal.ofReal (1 - δ) *
        (ProbabilityTheory.cond (annealedCoupledLaw Q.measure K) {q | q.2.2 0 = false})
          {q | q.2.1 ∈ tubeEvent (Renewal.forceCoord hd) lam l} := by
  let μ := annealedCoupledLaw Q.measure K
  have : IsProbabilityMeasure μ := annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  let B : Set (FieldPair d × CoupledSample d) := {q | q.2.2 0 = false}
  let T : Set (FieldPair d × CoupledSample d) :=
    {q | q.2.1 ∈ tubeEvent (Renewal.forceCoord hd) lam l}
  have hB : MeasurableSet B :=
    ((measurable_pi_apply (X := fun _ : ℕ => Bool) 0).comp measurable_snd.snd)
      (measurableSet_singleton false)
  have hinter : μ (B ∩ T) = μ T := by
    apply measure_congr
    filter_upwards [tubeEvent_bit_zero_false_ae hd Q lam h₀ h₁ l δ hl P K hK] with q hq
    exact propext (and_iff_right_of_imp hq)
  have hc := ProbabilityTheory.cond_mul_eq_inter hB T μ
  rw [hinter, bit_zero_false_mass hd Q lam h₀ h₁ l δ hδ P K hK] at hc
  exact hc.symm.trans (mul_comm _ _)

include hindep h₀ h₁ hl hsep hδ hδ₁ hK hD in
/-- The spatial past/future integral contains the exact no-return mass factor.
The lower half-space contributes zero; on the upper half-space the supplied
joint finite-range statement factors the two actual quenched integrals. -/
theorem firstSlice_spatial_mass_factorization (n : ℕ) (hn : 2 ≤ n)
    (H : CoupledSample d → ℝ)
    (hH : Measurable[finiteHistorySigma (Renewal.regenDelta lam) (n - 1)] H)
    (hbH : BoundedRealTest H) :
    (∫ y, ∫ ω,
      firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
          (Renewal.forceCoord hd) (n - 1) K H (y, ω) *
        (∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd)
          (fun _ => (1 : ℝ)) ((y, ω), z) ∂K (y, ω)) ∂Q.measure) =
      (∫ y, ∫ ω, firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
          (Renewal.forceCoord hd) (n - 1) K H (y, ω) ∂Q.measure) *
        (annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam))).toReal := by
  have hdata := ((hindep d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD
    (fun _ => (1 : ℝ)) measurable_const ⟨1, by simp⟩).1
      (fun _ => (1 : ℝ)) measurable_const ⟨1, by simp⟩ n hn H hH hbH)
  obtain ⟨_, hzero, hprod, hmean, _⟩ := hdata
  simp only [one_mul] at hzero hprod
  have hfactor : ∀ᵐ y ∂(volume : Measure (Vec d)),
      (∫ ω,
        firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
            (Renewal.forceCoord hd) (n - 1) K H (y, ω) *
          (∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd)
            (fun _ => (1 : ℝ)) ((y, ω), z) ∂K (y, ω)) ∂Q.measure) =
        (∫ ω, firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
            (Renewal.forceCoord hd) (n - 1) K H (y, ω) ∂Q.measure) *
          (annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam))).toReal := by
    filter_upwards [hzero, hprod, hmean] with y hz hp hm
    have hm' : (∫ ω, (∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd)
        (fun _ => (1 : ℝ)) ((y, ω), z) ∂K (y, ω)) ∂Q.measure) =
        (annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam))).toReal := by
      simpa only [integral_const, smul_eq_mul, mul_one, measureReal_def,
        Measure.restrict_apply_univ] using hm
    by_cases hy : y (Renewal.forceCoord hd) < 10 * (l / lam)
    · have hz' := hz hy
      have hleft := integral_congr_ae (hz'.mono fun ω hω =>
        congrArg (fun a : ℝ => a * (∫ z, killedFutureTest (l / lam)
          (Renewal.forceCoord hd) (fun _ => (1 : ℝ)) ((y, ω), z) ∂K (y, ω))) hω)
      rw [hleft, integral_congr_ae hz']
      simp only [Pi.zero_apply, zero_mul, integral_zero]
    · rw [(hp (le_of_not_gt hy)).2, hm']
  rw [integral_congr_ae hfactor, integral_mul_const]

include hindep h₀ h₁ hl hsep hδ hδ₁ hK hD in
/-- The first-slice mass identity for an arbitrary bounded past test. The
no-return factor follows from joint finite range after endpoint Fubini. -/
theorem firstSlice_past_mass_factorization (n : ℕ) (hn : 2 ≤ n)
    (H : CoupledSample d → ℝ)
    (hH : Measurable[finiteHistorySigma (Renewal.regenDelta lam) (n - 1)] H)
    (hbH : BoundedRealTest H) :
    (∫ q in {q : FieldPair d × CoupledSample d |
        firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
          (Renewal.forceCoord hd) =
            (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      H q.2 ∂annealedCoupledLaw Q.measure K) =
      δ * (∫ q, ((forcedBitTrialEvent (Renewal.regenDelta lam) lam (l / lam)
          (Renewal.forceCoord hd) (n - 1)).indicator H) q.2
        ∂annealedCoupledLaw Q.measure K) *
        (annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam))).toReal := by
  have hR : 0 < l / lam := div_pos hl h₀
  have hΔ : 0 < Renewal.regenDelta lam :=
    Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  obtain ⟨C, _, B, hB, hbB, _, hBp⟩ :=
    exists_globally_bounded_measurable_killed_future_version Q.measure K hK.1
      (l / lam) (Renewal.forceCoord hd) (fun _ => (1 : ℝ)) measurable_const ⟨1, by simp⟩
  have hBp' : ∀ᵐ yω ∂(volume : Measure (Vec d)).prod Q.measure,
      B yω = ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd)
        (fun _ => (1 : ℝ)) (yω, z) ∂K yω := hBp
  have hs := firstRegeneration_slice_integral_eq hd Q lam h₀.le h₁ P K
    hK.1 hK.2.1 hK.2.2.1 (Renewal.regenDelta lam) hΔ
    δ (l / lam) hR (Renewal.forceCoord hd) hK.2.2.2.2.1 hK.2.2.2.2.2.2.1
    (fun _ => (1 : ℝ)) measurable_const ⟨1, by simp⟩ B hB ⟨C, hbB⟩ hBp'
    (n - 1) H hH hbH
  have hn' : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
  simp only [mul_one, hn'] at hs
  rw [hs]
  have hreplace :
      (∫ y, ∫ ω, firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
          (Renewal.forceCoord hd) (n - 1) K H (y, ω) * B (y, ω) ∂Q.measure) =
      ∫ y, ∫ ω, firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
          (Renewal.forceCoord hd) (n - 1) K H (y, ω) *
        (∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd)
          (fun _ => (1 : ℝ)) ((y, ω), z) ∂K (y, ω)) ∂Q.measure := by
    apply integral_congr_ae
    filter_upwards [MeasureTheory.Measure.ae_ae_of_ae_prod hBp'] with y hy
    exact integral_congr_ae (hy.mono fun ω hω => congrArg
      (fun b : ℝ => firstSlicePastIntegral (Renewal.regenDelta lam) lam (l / lam)
        (Renewal.forceCoord hd) (n - 1) K H (y, ω) * b) hω)
  rw [hreplace, firstSlice_spatial_mass_factorization hindep hd Q lam h₀ h₁ l δ
    hl hsep hδ hδ₁ P K hK hD n hn H hH hbH]
  rw [div_eq_mul_inv, ← mul_assoc, mul_assoc δ]
  rw [spatial_past_mass_eq Q.measure K hK.1 (Renewal.regenDelta lam)
    hΔ lam (l / lam) hR (Renewal.forceCoord hd)
    (n - 1) H hH hbH]

/-- The first literal tube together with the first regeneration slice at `2Δ`. -/
def firstTubeSlice {d : ℕ} (hd : 2 ≤ d) (lam l : ℝ) :
    Set (FieldPair d × CoupledSample d) :=
  {q | q.2.1 ∈ tubeEvent (Renewal.forceCoord hd) lam l ∧
    firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
      (Renewal.forceCoord hd) = ((2 * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)}

/-- Both the all-time tube and the exact regeneration slice are measurable. -/
theorem measurableSet_firstTubeSlice {d : ℕ} (hd : 2 ≤ d) (lam l : ℝ) :
    MeasurableSet (firstTubeSlice hd lam l) :=
  ((measurableSet_tubeEvent (Renewal.forceCoord hd) lam l).preimage
      measurable_snd.fst).inter
    (measurableSet_eq_fun ((measurable_firstRegenerationTime _ _ _ _).comp
      measurable_snd) measurable_const)

include hindep h₀ h₁ hl hsep hδ hδ₁ hK hD in
/-- Exact raw mass of the tube-restricted first slice. No independence of
the tube and no-return events is used. -/
theorem firstTubeSlice_mass :
    annealedCoupledLaw Q.measure K (firstTubeSlice hd lam l) =
      ENNReal.ofReal δ * annealedCoupledLaw Q.measure K
        {q | q.2.1 ∈ tubeEvent (Renewal.forceCoord hd) lam l} *
      annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) := by
  let μ := annealedCoupledLaw Q.measure K
  have : IsProbabilityMeasure μ := annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  let A : Set (CoupledSample d) := {z | z.1 ∈ tubeEvent (Renewal.forceCoord hd) lam l}
  let T : Set (FieldPair d × CoupledSample d) := {q | q.2 ∈ A}
  let H : CoupledSample d → ℝ := A.indicator (fun _ => (1 : ℝ))
  have hA := measurableSet_tubeEvent_history (Renewal.forceCoord hd) lam l
  have hH : Measurable[finiteHistorySigma (Renewal.regenDelta lam) (2 - 1)] H := by
    exact measurable_const.indicator hA
  have hbH : BoundedRealTest H := by
    refine ⟨1, fun z => ?_⟩
    by_cases hz : z ∈ A <;> simp [H, hz]
  have hT : MeasurableSet T :=
    ((measurableSet_tubeEvent (Renewal.forceCoord hd) lam l).preimage measurable_fst).preimage
      measurable_snd
  have hstart := ae_origin_start_of_isGMPReducedKernel hd Q lam h₀.le h₁ P K
    hK.1 hK.2.1 hK.2.2.1
  have hforced :
      (∫ q, ((forcedBitTrialEvent (Renewal.regenDelta lam) lam (l / lam)
          (Renewal.forceCoord hd) 1).indicator H) q.2 ∂μ) = (μ T).toReal := by
    calc
      _ = ∫ q, H q.2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [hstart] with q hq
        by_cases ht : q.2 ∈ A
        · exact Set.indicator_of_mem (tubeEvent_mem_forcedBitTrialEvent hd h₀ h₁ hl
            q.2 hq ht) H
        · by_cases hf : q.2 ∈ forcedBitTrialEvent (Renewal.regenDelta lam) lam
              (l / lam) (Renewal.forceCoord hd) 1 <;> simp [hf, H, ht]
      _ = _ := by
        change (∫ q, T.indicator (fun _ => (1 : ℝ)) q ∂μ) = _
        rw [integral_indicator hT]
        simp only [integral_const, smul_eq_mul, mul_one, measureReal_def,
          Measure.restrict_apply_univ]
  have hraw := firstSlice_past_mass_factorization hindep hd Q lam h₀ h₁ l δ
    hl hsep hδ hδ₁ P K hK hD 2 (by omega) H hH hbH
  simp only [Nat.reduceSub, Nat.cast_ofNat] at hraw
  rw [hforced] at hraw
  have hleft : (∫ q in {q : FieldPair d × CoupledSample d |
      firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
        (Renewal.forceCoord hd) = ((2 * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      H q.2 ∂μ) = (μ (firstTubeSlice hd lam l)).toReal := by
    change (∫ q in _, T.indicator (fun _ => (1 : ℝ)) q ∂μ) = _
    rw [integral_indicator hT]
    simp only [integral_const, smul_eq_mul, mul_one, measureReal_def,
      Measure.restrict_apply_univ, Measure.restrict_apply hT]
    rfl
  rw [hleft] at hraw
  change μ (firstTubeSlice hd lam l) = ENNReal.ofReal δ * μ T * _
  calc
    _ = ENNReal.ofReal (μ (firstTubeSlice hd lam l)).toReal :=
      (ENNReal.ofReal_toReal (measure_ne_top μ _)).symm
    _ = ENNReal.ofReal (δ * (μ T).toReal *
        (μ (regenerationNoReturn hd (l / lam))).toReal) := congrArg ENNReal.ofReal hraw
    _ = _ := by
      rw [ENNReal.ofReal_mul (mul_nonneg hδ.le ENNReal.toReal_nonneg),
        ENNReal.ofReal_mul hδ.le, ENNReal.ofReal_toReal (measure_ne_top μ T),
        ENNReal.ofReal_toReal (measure_ne_top μ _)]

include hindep h₀ h₁ hl hsep hδ hδ₁ hK hD in
/-- The raw slice retains both coin probabilities and the independently
justified no-return mass, with the tube law conditioned on the first false bit. -/
theorem firstTubeSlice_two_coin_mass :
    annealedCoupledLaw Q.measure K (firstTubeSlice hd lam l) =
      ENNReal.ofReal δ * ENNReal.ofReal (1 - δ) *
        (ProbabilityTheory.cond (annealedCoupledLaw Q.measure K) {q | q.2.2 0 = false})
          {q | q.2.1 ∈ tubeEvent (Renewal.forceCoord hd) lam l} *
        annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) := by
  rw [firstTubeSlice_mass hindep hd Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD,
    tubeEvent_mass_eq_false_zero_cond hd Q lam h₀ h₁ l δ hl hδ P K hK,
    ← mul_assoc]

include h₀ h₁ hl hK in
/-- On the first tube slice, prebridge survival gives the actual no-return
event almost everywhere under the annealed coupling. -/
theorem firstTubeSlice_noReturn_ae :
    ∀ᵐ q ∂annealedCoupledLaw Q.measure K,
      q ∈ firstTubeSlice hd lam l → q ∈ regenerationNoReturn hd (l / lam) := by
  have hstart := ae_origin_start_of_isGMPReducedKernel hd Q lam h₀.le h₁ P K
    hK.1 hK.2.1 hK.2.2.1
  have hbar := c1_prebridge_survival hd Q lam h₀ h₁ l δ hl P K hK 2 (by omega)
  filter_upwards [hstart, hbar] with q hq0 hq
  intro ht
  have hgeo := node_rt_u3A_renewal_u23_tube_u2D_geometry_of_deps d hd l hl lam h₀ h₁
    2 (Or.inl rfl) q.2.1 hq0 (by
      intro u hu
      have hu' : (u : ℝ) ≤ 1 := by norm_num at hu; exact hu
      simpa only [tubeCurve, ite_true] using ht.1 u hu')
  apply (hq (by
    simpa only [EinsteinFull.regenerationTime, regenerationTime_one, Nat.cast_ofNat]
      using ht.2)).2
  exact hgeo.2.2.2.2

include hindep h₀ h₁ hl hsep hδ hδ₁ hK hD in
/-- Conditioning on no return cancels its strictly positive mass after
the spatial factorization; the remaining tube factor is the actual path mass. -/
theorem conditioned_firstTubeSlice_mass :
    (regenerationConditionedLaw hd Q lam l K hK.1 hD) (firstTubeSlice hd lam l) =
      ENNReal.ofReal δ * annealedCoupledLaw Q.measure K
        {q | q.2.1 ∈ tubeEvent (Renewal.forceCoord hd) lam l} := by
  let μ := annealedCoupledLaw Q.measure K
  have : IsProbabilityMeasure μ := annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have hinter : μ (regenerationNoReturn hd (l / lam) ∩ firstTubeSlice hd lam l) =
      μ (firstTubeSlice hd lam l) := by
    apply measure_congr
    filter_upwards [firstTubeSlice_noReturn_ae hd Q lam h₀ h₁ l δ hl P K hK] with q hq
    exact propext (and_iff_right_of_imp hq)
  rw [EinsteinFull.regenerationConditionedLaw_eq_cond,
    ProbabilityTheory.cond_apply' (measurableSet_firstTubeSlice hd lam l)]
  change (μ (regenerationNoReturn hd (l / lam)))⁻¹ *
    μ (regenerationNoReturn hd (l / lam) ∩ firstTubeSlice hd lam l) = _
  rw [hinter, firstTubeSlice_mass hindep hd Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD]
  change (μ (regenerationNoReturn hd (l / lam)))⁻¹ *
    (ENNReal.ofReal δ * μ _ * μ (regenerationNoReturn hd (l / lam))) = _
  calc
    _ = (μ (regenerationNoReturn hd (l / lam)))⁻¹ *
        μ (regenerationNoReturn hd (l / lam)) * (ENNReal.ofReal δ * μ _) := by ac_rfl
    _ = _ := by rw [ENNReal.inv_mul_cancel hD (measure_ne_top μ _), one_mul]

include hindep h₀ h₁ hl hsep hδ hδ₁ hK hD in
/-- Both coin factors, with the remaining tube mass conditioned on the
initial false bit. The no-return factor has already been justified and canceled. -/
theorem conditioned_firstTubeSlice_two_coin_mass :
    (regenerationConditionedLaw hd Q lam l K hK.1 hD) (firstTubeSlice hd lam l) =
      ENNReal.ofReal δ * ENNReal.ofReal (1 - δ) *
        (ProbabilityTheory.cond (annealedCoupledLaw Q.measure K) {q | q.2.2 0 = false})
          {q | q.2.1 ∈ tubeEvent (Renewal.forceCoord hd) lam l} := by
  rw [conditioned_firstTubeSlice_mass hindep hd Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD,
    tubeEvent_mass_eq_false_zero_cond hd Q lam h₀ h₁ l δ hl hδ P K hK,
    ← mul_assoc]

include h₀ h₁ hl hδ hδ₁ hK in
/-- A mesh bound under the actual law gives the correctly normalized bound
under conditioning on the initial false bit. Its exact weight is retained. -/
theorem tubeEvent_false_zero_cond_mass_lower_of_step_minorization (η : ℝ≥0∞)
    (hstep : ∀ᵐ ω ∂Q.measure, ∀ k : ℕ, k < 3200 → ∀ y : Vec d,
      euclideanNorm (lam • y - tubeCenters (Renewal.forceCoord hd) l k) < (l / 32) / 16 →
        η ≤ P (y, ω) (meshPiece lam (l / 32) (tubeStepTime lam)
          (tubeCenters (Renewal.forceCoord hd) l) k)) :
    (ENNReal.ofReal (1 - δ))⁻¹ * η ^ 3200 ≤
      (ProbabilityTheory.cond (annealedCoupledLaw Q.measure K) {q | q.2.2 0 = false})
        {q | q.2.1 ∈ tubeEvent (Renewal.forceCoord hd) lam l} := by
  have hpath := ae_quenched_tubeEvent_mass_lower hd Q.ellipticity_parameter Q lam h₀.le
    h₁ h₀ P hK.2.2.1 (Renewal.forceCoord hd) l hl η hstep
  have hmass := annealed_tubeEvent_mass_lower Q.measure K P hK.1 hK.2.1
    (Renewal.forceCoord hd) lam l (η ^ 3200) hpath
  calc
    _ ≤ (ENNReal.ofReal (1 - δ))⁻¹ *
        annealedCoupledLaw Q.measure K {q | q.2.1 ∈ tubeEvent (Renewal.forceCoord hd) lam l} :=
      mul_le_mul' le_rfl hmass
    _ = _ := by
      rw [tubeEvent_mass_eq_false_zero_cond hd Q lam h₀ h₁ l δ hl hδ P K hK,
        ← mul_assoc, ENNReal.inv_mul_cancel
          (ENNReal.ofReal_pos.mpr (sub_pos.mpr hδ₁)).ne' ENNReal.ofReal_ne_top, one_mul]

include hindep h₀ h₁ hl hsep hδ hδ₁ hK hD in
/-- Quantitative first-slice bound with both literal coin weights and the
normalization of the initial-false conditional tube probability. -/
theorem conditioned_firstTubeSlice_mass_lower_of_step_minorization (η : ℝ≥0∞)
    (hstep : ∀ᵐ ω ∂Q.measure, ∀ k : ℕ, k < 3200 → ∀ y : Vec d,
      euclideanNorm (lam • y - tubeCenters (Renewal.forceCoord hd) l k) < (l / 32) / 16 →
        η ≤ P (y, ω) (meshPiece lam (l / 32) (tubeStepTime lam)
          (tubeCenters (Renewal.forceCoord hd) l) k)) :
    ENNReal.ofReal δ * ENNReal.ofReal (1 - δ) *
      ((ENNReal.ofReal (1 - δ))⁻¹ * η ^ 3200) ≤
      (regenerationConditionedLaw hd Q lam l K hK.1 hD) (firstTubeSlice hd lam l) := by
  rw [conditioned_firstTubeSlice_two_coin_mass hindep hd Q lam h₀ h₁ l δ hl hsep hδ hδ₁
    P K hK hD]
  exact mul_le_mul' le_rfl
    (tubeEvent_false_zero_cond_mass_lower_of_step_minorization hd Q lam h₀ h₁ l δ hl
      hδ hδ₁ P K hK η hstep)

include hindep h₀ h₁ hl hsep hδ hδ₁ hK hD in
/-- Actual killed endpoint domination composes all the way to the quantitative
no-return-conditioned first slice, without changing either coin weight. -/
theorem conditioned_firstTubeSlice_mass_lower_of_killed_domination (a : ℝ≥0∞)
    (hdom : ∀ᵐ ω ∂Q.measure, ∀ k : ℕ, k < 3200 → ∀ y : Vec d,
      euclideanNorm (lam • y - tubeCenters (Renewal.forceCoord hd) l k) < (l / 32) / 16 →
      a • (volume : Measure (Vec d)).restrict (meshBall lam ((l / 32) / 16)
          (tubeCenters (Renewal.forceCoord hd) l (k + 1))) ≤
        ((P (y, ω)).restrict {γ | (tubeStepTime lam : ℝ≥0∞) <
          Diffusion.localityExitTime (meshBall lam ((l / 32) / 2)
            (tubeCenters (Renewal.forceCoord hd) l k)) γ}).map
          (pathPosition (tubeStepTime lam))) :
    ENNReal.ofReal δ * ENNReal.ofReal (1 - δ) *
      ((ENNReal.ofReal (1 - δ))⁻¹ *
        (a * volume (meshBall lam ((l / 32) / 16) (0 : Vec d))) ^ 3200) ≤
      (regenerationConditionedLaw hd Q lam l K hK.1 hD) (firstTubeSlice hd lam l) := by
  apply conditioned_firstTubeSlice_mass_lower_of_step_minorization hindep hd Q lam h₀ h₁
    l δ hl hsep hδ hδ₁ P K hK hD
  exact ae_meshPiece_mass_lower_of_killed_domination (by omega) Q.measure P h₀
    (l / 32) (tubeStepTime lam) (tubeCenters (Renewal.forceCoord hd) l) 3200 a hdom

include hindep h₀ h₁ hl hsep hδ hδ₁ hK hD in
/-- Ordinary closed-block minorization gives a strictly positive actual
first tube slice under no-return conditioning. -/
theorem conditioned_firstTubeSlice_pos_of_step_minorization (η : ℝ≥0∞) (hη : 0 < η)
    (hstep : ∀ᵐ ω ∂Q.measure, ∀ k : ℕ, k < 3200 → ∀ y : Vec d,
      euclideanNorm (lam • y - tubeCenters (Renewal.forceCoord hd) l k) < (l / 32) / 16 →
        η ≤ P (y, ω) (meshPiece lam (l / 32) (tubeStepTime lam)
          (tubeCenters (Renewal.forceCoord hd) l) k)) :
    0 < (regenerationConditionedLaw hd Q lam l K hK.1 hD) (firstTubeSlice hd lam l) := by
  rw [conditioned_firstTubeSlice_mass hindep hd Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD]
  have hpath := ae_quenched_tubeEvent_mass_lower hd Q.ellipticity_parameter Q lam h₀.le
    h₁ h₀ P hK.2.2.1 (Renewal.forceCoord hd) l hl η hstep
  have hmass := annealed_tubeEvent_mass_lower Q.measure K P hK.1 hK.2.1
    (Renewal.forceCoord hd) lam l (η ^ 3200) hpath
  exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hδ).ne'
    (lt_of_lt_of_le (bot_lt_iff_ne_bot.mpr (pow_ne_zero 3200 hη.ne')) hmass).ne'

include hindep h₀ h₁ hl hsep hδ hδ₁ hK hD in
/-- A strictly positive common domination coefficient makes the actual
conditioned first slice strictly positive at every admissible original scale. -/
theorem conditioned_firstTubeSlice_pos_of_killed_domination (a : ℝ≥0∞) (ha : 0 < a)
    (hdom : ∀ᵐ ω ∂Q.measure, ∀ k : ℕ, k < 3200 → ∀ y : Vec d,
      euclideanNorm (lam • y - tubeCenters (Renewal.forceCoord hd) l k) < (l / 32) / 16 →
      a • (volume : Measure (Vec d)).restrict (meshBall lam ((l / 32) / 16)
          (tubeCenters (Renewal.forceCoord hd) l (k + 1))) ≤
        ((P (y, ω)).restrict {γ | (tubeStepTime lam : ℝ≥0∞) <
          Diffusion.localityExitTime (meshBall lam ((l / 32) / 2)
            (tubeCenters (Renewal.forceCoord hd) l k)) γ}).map
          (pathPosition (tubeStepTime lam))) :
    0 < (regenerationConditionedLaw hd Q lam l K hK.1 hD) (firstTubeSlice hd lam l) := by
  have hvol := volume_meshBall_pos h₀
    (show 0 < (l / 32) / 16 by positivity) (0 : Vec d)
  apply conditioned_firstTubeSlice_pos_of_step_minorization hindep hd Q lam h₀ h₁
    l δ hl hsep hδ hδ₁ P K hK hD
    (a * volume (meshBall lam ((l / 32) / 16) (0 : Vec d)))
    (ENNReal.mul_pos ha.ne' hvol.ne')
  exact ae_meshPiece_mass_lower_of_killed_domination (by omega) Q.measure P h₀
    (l / 32) (tubeStepTime lam) (tubeCenters (Renewal.forceCoord hd) l) 3200 a hdom

include hindep h₀ h₁ hl hsep hδ hδ₁ hK hD in
/-- The exact spatial slice factorization converts positive actual annealed
 tube mass into almost-sure finiteness of the first regeneration time. -/
theorem first_finite_of_tube_mass_pos
    (hpath : 0 < annealedCoupledLaw Q.measure K
      {q | q.2.1 ∈ tubeEvent (Renewal.forceCoord hd) lam l}) :
    ∀ᵐ q ∂annealedCoupledLaw Q.measure K,
      firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
        (Renewal.forceCoord hd) ≠ ⊤ := by
  apply (sbx_s6_first_finite_iff_conditioned_positive hindep hd Q lam h₀ h₁ l δ
    hl hsep hδ hδ₁ P K hK hD).2
  have hpos : 0 < (regenerationConditionedLaw hd Q lam l K hK.1 hD)
      (firstTubeSlice hd lam l) := by
    rw [conditioned_firstTubeSlice_mass hindep hd Q lam h₀ h₁ l δ
      hl hsep hδ hδ₁ P K hK hD]
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hδ).ne' hpath.ne'
  apply ne_of_gt (lt_of_lt_of_le hpos (measure_mono ?_))
  intro q hq
  change firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
    (Renewal.forceCoord hd) ≠ ⊤
  rw [hq.2]
  exact ENNReal.coe_ne_top

include hindep h₀ h₁ hl hsep hδ hδ₁ hK hD in
/-- The positive finite slice discharges the existing conditioned-positivity
criterion. The analytic hypotheses remain explicit one-block estimates. -/
theorem first_finite_of_step_minorization (η : ℝ≥0∞) (hη : 0 < η)
    (hstep : ∀ᵐ ω ∂Q.measure, ∀ k : ℕ, k < 3200 → ∀ y : Vec d,
      euclideanNorm (lam • y - tubeCenters (Renewal.forceCoord hd) l k) < (l / 32) / 16 →
        η ≤ P (y, ω) (meshPiece lam (l / 32) (tubeStepTime lam)
          (tubeCenters (Renewal.forceCoord hd) l) k)) :
    ∀ᵐ q ∂annealedCoupledLaw Q.measure K,
      firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
        (Renewal.forceCoord hd) ≠ ⊤ := by
  apply (sbx_s6_first_finite_iff_conditioned_positive hindep hd Q lam h₀ h₁ l δ
    hl hsep hδ hδ₁ P K hK hD).2
  have hpos := conditioned_firstTubeSlice_pos_of_step_minorization hindep hd Q lam
    h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD η hη hstep
  apply ne_of_gt (lt_of_lt_of_le hpos (measure_mono ?_))
  intro q hq
  change firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
    (Renewal.forceCoord hd) ≠ ⊤
  rw [hq.2]
  exact ENNReal.coe_ne_top

include hindep h₀ h₁ hl hsep hδ hδ₁ hK hD in
/-- Almost-sure finiteness of the actual first time propagates to finite cycles,
all record laws and one invariant measurable shift under both source laws. -/
theorem all_record_iteration_of_first_finite
    (hfin : ∀ᵐ q ∂annealedCoupledLaw Q.measure K,
      firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
        (Renewal.forceCoord hd) ≠ ⊤) :
    let μ := annealedCoupledLaw Q.measure K
    let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
    (∀ ρ ∈ ({μ, ν} : Set (Measure (FieldPair d × CoupledSample d))),
      ∀ k : ℕ, ∀ᵐ q ∂ρ, EinsteinFull.regenerationTime hd lam l k q.2 ≠ ⊤) ∧
    (∀ ρ ∈ ({μ, ν} : Set (Measure (FieldPair d × CoupledSample d))),
      ∀ k : ℕ, 1 ≤ k →
        ρ.map (regenerationRecord hd lam l k) = ν.map (regenerationRecord hd lam l 0)) ∧
    ∃ Θ : FutureState d (Renewal.forceCoord hd) (l / lam) →
        FutureState d (Renewal.forceCoord hd) (l / lam),
      Measurable Θ ∧
      (∀ ρ ∈ ({μ, ν} : Set (Measure (FieldPair d × CoupledSample d))),
        ∀ k : ℕ, ∀ᵐ q ∂ρ,
          Θ (regenerationRecord hd lam l k q) = regenerationRecord hd lam l (k + 1) q) ∧
      (ν.map (regenerationRecord hd lam l 0)).map Θ =
        ν.map (regenerationRecord hd lam l 0) := by
  let μ := annealedCoupledLaw Q.measure K
  let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
  let Δ := Renewal.regenDelta lam
  let R := l / lam
  let i := Renewal.forceCoord hd
  have hΔ : 0 < Δ := Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have hνμ : ν ≪ μ :=
    EinsteinFull.regenerationConditionedLaw_absolutelyContinuous hd Q lam l K hK.1 hD
  have hfwd := ae_firstRegenerationTime_forward Q.measure K hK.1 Δ hΔ lam R h₀
    (div_pos hl h₀) i hK.2.2.2.2.2.1
  have hgood : ∀ᵐ q ∂μ, RecordCanShift Δ lam R i (iteratedRecord Δ lam R i 0 q) := by
    filter_upwards [hfin, hfwd] with q hq hforward
    change RecordCanShift Δ lam R i (futureRecord Δ R q.1 q.2 i 0)
    rw [recordCanShift_futureRecord_iff, sampleTimeShift_zero, zero_add]
    exact ⟨hq, hforward hq⟩
  have hfirst : μ.map (iteratedRecord Δ lam R i 1) = ν.map (iteratedRecord Δ lam R i 0) :=
    sbx_s6_annealed_first_law hindep hd Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD
  have hcond : ν.map (iteratedRecord Δ lam R i 1) = ν.map (iteratedRecord Δ lam R i 0) :=
    sbx_s6_conditional_first_law hindep hd Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD
  have hiter := iteratedRecord_law_of_first_and_conditional_law Δ hΔ lam R i μ ν
    hνμ hgood hfirst hcond
  have hfiniteall : ∀ ρ ∈ ({μ, ν} : Set (Measure (FieldPair d × CoupledSample d))),
      ∀ k : ℕ, ∀ᵐ q ∂ρ, EinsteinFull.regenerationTime hd lam l k q.2 ≠ ⊤ := by
    have hall : ∀ k : ℕ, ∀ᵐ q ∂μ, EinsteinFull.regenerationTime hd lam l k q.2 ≠ ⊤ := by
      intro k
      cases k with
      | zero => exact Filter.Eventually.of_forall fun _ => ENNReal.zero_ne_top
      | succ j => exact (hiter j).1
    intro ρ hρ k
    rcases Set.mem_insert_iff.mp hρ with rfl | hρ
    · exact hall k
    · obtain rfl := Set.mem_singleton_iff.mp hρ
      exact hνμ.ae_le (hall k)
  have hlaws : ∀ ρ ∈ ({μ, ν} : Set (Measure (FieldPair d × CoupledSample d))),
      ∀ k : ℕ, 1 ≤ k →
        ρ.map (regenerationRecord hd lam l k) = ν.map (regenerationRecord hd lam l 0) := by
    intro ρ hρ k hk
    rcases Set.mem_insert_iff.mp hρ with rfl | hρ
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      exact (hiter j).2
    · obtain rfl := Set.mem_singleton_iff.mp hρ
      exact sbx_s6_conditional_all_record_laws hindep hd Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD k
  obtain ⟨D, hDm, hdecode⟩ := Probability.exists_future_halfSpace_decoder i R
  let Θ := shiftRestrictedRecord Δ lam R i D
  have hΘ : Measurable Θ := measurable_shiftRestrictedRecord Δ lam R i D hDm
  have hσgood : ∀ᵐ y ∂ν.map (iteratedRecord Δ lam R i 0), RecordCanShift Δ lam R i y :=
    (ae_map_iff (measurable_iteratedRecord Δ lam R i 0).aemeasurable
      (measurableSet_recordCanShift Δ lam R i)).mpr (hνμ.ae_le hgood)
  have hcompose : ∀ k : ℕ, ∀ᵐ q ∂μ,
      Θ (regenerationRecord hd lam l k q) = regenerationRecord hd lam l (k + 1) q := by
    intro k
    have hkgood : ∀ᵐ q ∂μ, RecordCanShift Δ lam R i (iteratedRecord Δ lam R i k q) := by
      cases k with
      | zero => exact hgood
      | succ j =>
          rw [← (hiter j).2] at hσgood
          exact ae_of_ae_map (measurable_iteratedRecord Δ lam R i (j + 1)).aemeasurable hσgood
    have hkfin : ∀ᵐ q ∂μ, Regeneration.regenerationTime Δ lam R q.2 i k ≠ ⊤ := by
      cases k with
      | zero => exact Filter.Eventually.of_forall fun _ => ENNReal.zero_ne_top
      | succ j => exact (hiter j).1
    filter_upwards [hkgood, hkfin] with q hq hqfin
    exact (iteratedRecord_succ_of_canShift Δ hΔ lam R i D hdecode q k hqfin hq).2.symm
  refine ⟨hfiniteall, hlaws, Θ, hΘ, ?_, ?_⟩
  · intro ρ hρ k
    rcases Set.mem_insert_iff.mp hρ with rfl | hρ
    · exact hcompose k
    · obtain rfl := Set.mem_singleton_iff.mp hρ
      exact hνμ.ae_le (hcompose k)
  · rw [Measure.map_map hΘ (EinsteinFull.measurable_regenerationRecord hd lam l 0)]
    exact (Measure.map_congr (hνμ.ae_le (hcompose 0))).trans hcond

include hindep h₀ h₁ hl hsep hδ hδ₁ hK hD in
/-- Positive actual annealed tube mass gives finite cycles, all actual record
laws, and one invariant measurable shift composing every record under both laws.
No uniform minorization constant is required by this consumer. -/
theorem all_record_iteration_of_tube_mass_pos
    (hpath : 0 < annealedCoupledLaw Q.measure K
      {q | q.2.1 ∈ tubeEvent (Renewal.forceCoord hd) lam l}) :
    let μ := annealedCoupledLaw Q.measure K
    let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
    (∀ ρ ∈ ({μ, ν} : Set (Measure (FieldPair d × CoupledSample d))),
      ∀ k : ℕ, ∀ᵐ q ∂ρ, EinsteinFull.regenerationTime hd lam l k q.2 ≠ ⊤) ∧
    (∀ ρ ∈ ({μ, ν} : Set (Measure (FieldPair d × CoupledSample d))),
      ∀ k : ℕ, 1 ≤ k →
        ρ.map (regenerationRecord hd lam l k) = ν.map (regenerationRecord hd lam l 0)) ∧
    ∃ Θ : FutureState d (Renewal.forceCoord hd) (l / lam) →
        FutureState d (Renewal.forceCoord hd) (l / lam),
      Measurable Θ ∧
      (∀ ρ ∈ ({μ, ν} : Set (Measure (FieldPair d × CoupledSample d))),
        ∀ k : ℕ, ∀ᵐ q ∂ρ,
          Θ (regenerationRecord hd lam l k q) = regenerationRecord hd lam l (k + 1) q) ∧
      (ν.map (regenerationRecord hd lam l 0)).map Θ =
        ν.map (regenerationRecord hd lam l 0) := by
  exact all_record_iteration_of_first_finite hindep hd Q lam h₀ h₁ l δ hl
    hsep hδ hδ₁ P K hK hD
    (first_finite_of_tube_mass_pos hindep hd Q lam h₀ h₁ l δ hl
      hsep hδ hδ₁ P K hK hD hpath)

include hindep h₀ h₁ hl hsep hδ hδ₁ hK hD in
/-- The previous quantitative interface follows by the finite product bound. -/
theorem all_record_iteration_of_step_minorization (η : ℝ≥0∞) (hη : 0 < η)
    (hstep : ∀ᵐ ω ∂Q.measure, ∀ k : ℕ, k < 3200 → ∀ y : Vec d,
      euclideanNorm (lam • y - tubeCenters (Renewal.forceCoord hd) l k) < (l / 32) / 16 →
        η ≤ P (y, ω) (meshPiece lam (l / 32) (tubeStepTime lam)
          (tubeCenters (Renewal.forceCoord hd) l) k)) :
    let μ := annealedCoupledLaw Q.measure K
    let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
    (∀ ρ ∈ ({μ, ν} : Set (Measure (FieldPair d × CoupledSample d))),
      ∀ k : ℕ, ∀ᵐ q ∂ρ, EinsteinFull.regenerationTime hd lam l k q.2 ≠ ⊤) ∧
    (∀ ρ ∈ ({μ, ν} : Set (Measure (FieldPair d × CoupledSample d))),
      ∀ k : ℕ, 1 ≤ k →
        ρ.map (regenerationRecord hd lam l k) = ν.map (regenerationRecord hd lam l 0)) ∧
    ∃ Θ : FutureState d (Renewal.forceCoord hd) (l / lam) →
        FutureState d (Renewal.forceCoord hd) (l / lam),
      Measurable Θ ∧
      (∀ ρ ∈ ({μ, ν} : Set (Measure (FieldPair d × CoupledSample d))),
        ∀ k : ℕ, ∀ᵐ q ∂ρ,
          Θ (regenerationRecord hd lam l k q) = regenerationRecord hd lam l (k + 1) q) ∧
      (ν.map (regenerationRecord hd lam l 0)).map Θ =
        ν.map (regenerationRecord hd lam l 0) := by
  have hpath := ae_quenched_tubeEvent_mass_lower hd Q.ellipticity_parameter Q lam h₀.le
    h₁ h₀ P hK.2.2.1 (Renewal.forceCoord hd) l hl η hstep
  have hmass := annealed_tubeEvent_mass_lower Q.measure K P hK.1 hK.2.1
    (Renewal.forceCoord hd) lam l (η ^ 3200) hpath
  have hpos := lt_of_lt_of_le
    (bot_lt_iff_ne_bot.mpr (pow_ne_zero 3200 hη.ne')) hmass
  exact all_record_iteration_of_tube_mass_pos hindep hd Q lam h₀ h₁ l δ hl
    hsep hδ hδ₁ P K hK hD hpos

include hindep h₀ h₁ hl hsep hδ hδ₁ hK hD in
/-- Finiteness of the actual first time suffices for the full pointwise
condition-iterate conclusion at the original scale. -/
theorem condition_iterate_of_first_finite
    (hfin : ∀ᵐ q ∂annealedCoupledLaw Q.measure K,
      firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
        (Renewal.forceCoord hd) ≠ ⊤) :
    let R := l / lam
    let i := Regeneration.Renewal.forceCoord hd
    let Δ := Regeneration.Renewal.regenDelta lam
    let μ := Regeneration.annealedCoupledLaw Q.measure K
    let ν := regenerationConditionedLaw hd Q lam l K
      hK.1 hD
    (∀ n : ℕ, 2 ≤ n → ∀ᵐ q ∂μ,
      EinsteinFull.regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) →
      (q ∈ regenerationNoReturn hd R ↔
        ∀ s : ℝ≥0, s ≤ (n - 1 : ℕ) * Δ → -R < q.2.1 s i)) ∧
    (∃ Θ : Regeneration.FutureState d i R → Regeneration.FutureState d i R,
      Measurable Θ ∧
      (∀ ρ ∈ ({μ, ν} : Set (Measure (FieldPair d × Regeneration.CoupledSample d))),
        ∀ k : ℕ, ∀ᵐ q ∂ρ,
          Θ (regenerationRecord hd lam l k q) = regenerationRecord hd lam l (k + 1) q) ∧
      Measure.map Θ (Measure.map (regenerationRecord hd lam l 0) ν) =
        Measure.map (regenerationRecord hd lam l 0) ν) ∧
    (∀ (Φ : Regeneration.FutureState d i R → ℝ),
      Measurable Φ → Regeneration.BoundedRealTest Φ →
      ∀ ρ ∈ ({μ, ν} : Set (Measure (FieldPair d × Regeneration.CoupledSample d))),
      (∀ k : ℕ, 1 ≤ k →
        (∫ q, Φ (regenerationRecord hd lam l k q) ∂ρ) =
          ∫ q, Φ (regenerationRecord hd lam l 0 q) ∂ν) ∧
      (∀ (F : FieldPair d → ℝ),
        Measurable[localSigma {x : Vec d | euclideanNorm x < R}] F →
        Regeneration.BoundedRealTest F →
        ∀ (n : ℕ), 2 ≤ n → ∀ (H : Regeneration.CoupledSample d → ℝ),
        Measurable[Regeneration.finiteHistorySigma Δ (n - 1)] H →
        Regeneration.BoundedRealTest H →
        (∫ q in {q | EinsteinFull.regenerationTime hd lam l 1 q.2 =
          (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)},
          F q.1 * H q.2 * Φ (regenerationRecord hd lam l 1 q) ∂ρ) =
        (∫ q in {q | EinsteinFull.regenerationTime hd lam l 1 q.2 =
          (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}, F q.1 * H q.2 ∂ρ) *
          ∫ q, Φ (regenerationRecord hd lam l 0 q) ∂ν)) := by
  obtain ⟨_, hlaws, hshift⟩ := all_record_iteration_of_first_finite hindep hd Q lam
    h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD hfin
  dsimp only
  refine ⟨?_, hshift, ?_⟩
  · intro n hn
    exact c1_prebridge_survival hd Q lam h₀ h₁ l δ hl P K hK n hn
  · intro Φ hΦ hbΦ ρ hρ
    refine ⟨?_, ?_⟩
    · intro k hk
      have hmap := hlaws ρ hρ k hk
      calc
        _ = ∫ y, Φ y ∂ρ.map (regenerationRecord hd lam l k) :=
          (integral_map (EinsteinFull.measurable_regenerationRecord hd lam l k).aemeasurable
            hΦ.aestronglyMeasurable).symm
        _ = ∫ y, Φ y ∂(regenerationConditionedLaw hd Q lam l K hK.1 hD).map
            (regenerationRecord hd lam l 0) := by rw [hmap]
        _ = _ := integral_map
          (EinsteinFull.measurable_regenerationRecord hd lam l 0).aemeasurable
          hΦ.aestronglyMeasurable
    · intro F hF hbF n hn H hH hbH
      exact sbx_s6_slice_factor_both hindep hd Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD
        Φ hΦ hbΦ F hF hbF n hn H hH hbH ρ hρ

include hindep h₀ h₁ hl hsep hδ hδ₁ hK hD in
/-- At a fixed admissible scale, positive actual annealed tube mass suffices
for the full condition-iterate conclusion. The tube positivity producer remains
explicit and this helper is not an exact graph-root reduction. -/
theorem condition_iterate_of_tube_mass_pos
    (hpath : 0 < annealedCoupledLaw Q.measure K
      {q | q.2.1 ∈ tubeEvent (Renewal.forceCoord hd) lam l}) :
    let R := l / lam
    let i := Regeneration.Renewal.forceCoord hd
    let Δ := Regeneration.Renewal.regenDelta lam
    let μ := Regeneration.annealedCoupledLaw Q.measure K
    let ν := regenerationConditionedLaw hd Q lam l K
      hK.1 hD
    (∀ n : ℕ, 2 ≤ n → ∀ᵐ q ∂μ,
      EinsteinFull.regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) →
      (q ∈ regenerationNoReturn hd R ↔
        ∀ s : ℝ≥0, s ≤ (n - 1 : ℕ) * Δ → -R < q.2.1 s i)) ∧
    (∃ Θ : Regeneration.FutureState d i R → Regeneration.FutureState d i R,
      Measurable Θ ∧
      (∀ ρ ∈ ({μ, ν} : Set (Measure (FieldPair d × Regeneration.CoupledSample d))),
        ∀ k : ℕ, ∀ᵐ q ∂ρ,
          Θ (regenerationRecord hd lam l k q) = regenerationRecord hd lam l (k + 1) q) ∧
      Measure.map Θ (Measure.map (regenerationRecord hd lam l 0) ν) =
        Measure.map (regenerationRecord hd lam l 0) ν) ∧
    (∀ (Φ : Regeneration.FutureState d i R → ℝ),
      Measurable Φ → Regeneration.BoundedRealTest Φ →
      ∀ ρ ∈ ({μ, ν} : Set (Measure (FieldPair d × Regeneration.CoupledSample d))),
      (∀ k : ℕ, 1 ≤ k →
        (∫ q, Φ (regenerationRecord hd lam l k q) ∂ρ) =
          ∫ q, Φ (regenerationRecord hd lam l 0 q) ∂ν) ∧
      (∀ (F : FieldPair d → ℝ),
        Measurable[localSigma {x : Vec d | euclideanNorm x < R}] F →
        Regeneration.BoundedRealTest F →
        ∀ (n : ℕ), 2 ≤ n → ∀ (H : Regeneration.CoupledSample d → ℝ),
        Measurable[Regeneration.finiteHistorySigma Δ (n - 1)] H →
        Regeneration.BoundedRealTest H →
        (∫ q in {q | EinsteinFull.regenerationTime hd lam l 1 q.2 =
          (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)},
          F q.1 * H q.2 * Φ (regenerationRecord hd lam l 1 q) ∂ρ) =
        (∫ q in {q | EinsteinFull.regenerationTime hd lam l 1 q.2 =
          (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}, F q.1 * H q.2 ∂ρ) *
          ∫ q, Φ (regenerationRecord hd lam l 0 q) ∂ν)) := by
  exact condition_iterate_of_first_finite hindep hd Q lam h₀ h₁ l δ hl
    hsep hδ hδ₁ P K hK hD
    (first_finite_of_tube_mass_pos hindep hd Q lam h₀ h₁ l δ hl
      hsep hδ hδ₁ P K hK hD hpath)

include hindep h₀ h₁ hl hsep hδ hδ₁ hK hD in
/-- Uniform ordinary block bounds imply the full conclusion through the
positive actual annealed tube mass. -/
theorem condition_iterate_of_step_minorization (η : ℝ≥0∞) (hη : 0 < η)
    (hstep : ∀ᵐ ω ∂Q.measure, ∀ k : ℕ, k < 3200 → ∀ y : Vec d,
      euclideanNorm (lam • y - tubeCenters (Renewal.forceCoord hd) l k) < (l / 32) / 16 →
        η ≤ P (y, ω) (meshPiece lam (l / 32) (tubeStepTime lam)
          (tubeCenters (Renewal.forceCoord hd) l) k)) :
    let R := l / lam
    let i := Regeneration.Renewal.forceCoord hd
    let Δ := Regeneration.Renewal.regenDelta lam
    let μ := Regeneration.annealedCoupledLaw Q.measure K
    let ν := regenerationConditionedLaw hd Q lam l K
      hK.1 hD
    (∀ n : ℕ, 2 ≤ n → ∀ᵐ q ∂μ,
      EinsteinFull.regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) →
      (q ∈ regenerationNoReturn hd R ↔
        ∀ s : ℝ≥0, s ≤ (n - 1 : ℕ) * Δ → -R < q.2.1 s i)) ∧
    (∃ Θ : Regeneration.FutureState d i R → Regeneration.FutureState d i R,
      Measurable Θ ∧
      (∀ ρ ∈ ({μ, ν} : Set (Measure (FieldPair d × Regeneration.CoupledSample d))),
        ∀ k : ℕ, ∀ᵐ q ∂ρ,
          Θ (regenerationRecord hd lam l k q) = regenerationRecord hd lam l (k + 1) q) ∧
      Measure.map Θ (Measure.map (regenerationRecord hd lam l 0) ν) =
        Measure.map (regenerationRecord hd lam l 0) ν) ∧
    (∀ (Φ : Regeneration.FutureState d i R → ℝ),
      Measurable Φ → Regeneration.BoundedRealTest Φ →
      ∀ ρ ∈ ({μ, ν} : Set (Measure (FieldPair d × Regeneration.CoupledSample d))),
      (∀ k : ℕ, 1 ≤ k →
        (∫ q, Φ (regenerationRecord hd lam l k q) ∂ρ) =
          ∫ q, Φ (regenerationRecord hd lam l 0 q) ∂ν) ∧
      (∀ (F : FieldPair d → ℝ),
        Measurable[localSigma {x : Vec d | euclideanNorm x < R}] F →
        Regeneration.BoundedRealTest F →
        ∀ (n : ℕ), 2 ≤ n → ∀ (H : Regeneration.CoupledSample d → ℝ),
        Measurable[Regeneration.finiteHistorySigma Δ (n - 1)] H →
        Regeneration.BoundedRealTest H →
        (∫ q in {q | EinsteinFull.regenerationTime hd lam l 1 q.2 =
          (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)},
          F q.1 * H q.2 * Φ (regenerationRecord hd lam l 1 q) ∂ρ) =
        (∫ q in {q | EinsteinFull.regenerationTime hd lam l 1 q.2 =
          (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}, F q.1 * H q.2 ∂ρ) *
          ∫ q, Φ (regenerationRecord hd lam l 0 q) ∂ν)) := by
  have hpath := ae_quenched_tubeEvent_mass_lower hd Q.ellipticity_parameter Q lam h₀.le
    h₁ h₀ P hK.2.2.1 (Renewal.forceCoord hd) l hl η hstep
  have hmass := annealed_tubeEvent_mass_lower Q.measure K P hK.1 hK.2.1
    (Renewal.forceCoord hd) lam l (η ^ 3200) hpath
  have hpos := lt_of_lt_of_le
    (bot_lt_iff_ne_bot.mpr (pow_ne_zero 3200 hη.ne')) hmass
  exact condition_iterate_of_tube_mass_pos hindep hd Q lam h₀ h₁ l δ hl
    hsep hδ hδ₁ P K hK hD hpos

include hindep h₀ h₁ hl hsep hδ hδ₁ hK hD in
/-- The precise qualitative analytic discharge site implies the complete
condition-iterate conclusion at the original admissible scale. Strict killed
positivity is still a hypothesis here, so this is not a graph-root reduction. -/
theorem condition_iterate_of_killed_ae_pos
    (hstep : ∀ᵐ ω ∂Q.measure, ∀ k : ℕ, k < 3200 →
      ∀ s : ℝ≥0, 0 < s → s ≤ tubeStepTime lam →
      ∀ᵐ y ∂(physicalReversibleMeasure ω hd lam).restrict
          (meshBall lam ((l / 32) / 2) (tubeCenters (Renewal.forceCoord hd) l k)),
        0 < Measure.map (pathPosition s)
          ((P (y, ω)).restrict {γ : Path d | (s : ℝ≥0∞) < Diffusion.localityExitTime
            (meshBall lam ((l / 32) / 2) (tubeCenters (Renewal.forceCoord hd) l k)) γ})
          (meshBall lam ((l / 32) / 16) (tubeCenters (Renewal.forceCoord hd) l (k + 1)))) :
    let R := l / lam
    let i := Regeneration.Renewal.forceCoord hd
    let Δ := Regeneration.Renewal.regenDelta lam
    let μ := Regeneration.annealedCoupledLaw Q.measure K
    let ν := regenerationConditionedLaw hd Q lam l K
      hK.1 hD
    (∀ n : ℕ, 2 ≤ n → ∀ᵐ q ∂μ,
      EinsteinFull.regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) →
      (q ∈ regenerationNoReturn hd R ↔
        ∀ s : ℝ≥0, s ≤ (n - 1 : ℕ) * Δ → -R < q.2.1 s i)) ∧
    (∃ Θ : Regeneration.FutureState d i R → Regeneration.FutureState d i R,
      Measurable Θ ∧
      (∀ ρ ∈ ({μ, ν} : Set (Measure (FieldPair d × Regeneration.CoupledSample d))),
        ∀ k : ℕ, ∀ᵐ q ∂ρ,
          Θ (regenerationRecord hd lam l k q) = regenerationRecord hd lam l (k + 1) q) ∧
      Measure.map Θ (Measure.map (regenerationRecord hd lam l 0) ν) =
        Measure.map (regenerationRecord hd lam l 0) ν) ∧
    (∀ (Φ : Regeneration.FutureState d i R → ℝ),
      Measurable Φ → Regeneration.BoundedRealTest Φ →
      ∀ ρ ∈ ({μ, ν} : Set (Measure (FieldPair d × Regeneration.CoupledSample d))),
      (∀ k : ℕ, 1 ≤ k →
        (∫ q, Φ (regenerationRecord hd lam l k q) ∂ρ) =
          ∫ q, Φ (regenerationRecord hd lam l 0 q) ∂ν) ∧
      (∀ (F : FieldPair d → ℝ),
        Measurable[localSigma {x : Vec d | euclideanNorm x < R}] F →
        Regeneration.BoundedRealTest F →
        ∀ (n : ℕ), 2 ≤ n → ∀ (H : Regeneration.CoupledSample d → ℝ),
        Measurable[Regeneration.finiteHistorySigma Δ (n - 1)] H →
        Regeneration.BoundedRealTest H →
        (∫ q in {q | EinsteinFull.regenerationTime hd lam l 1 q.2 =
          (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)},
          F q.1 * H q.2 * Φ (regenerationRecord hd lam l 1 q) ∂ρ) =
        (∫ q in {q | EinsteinFull.regenerationTime hd lam l 1 q.2 =
          (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}, F q.1 * H q.2 ∂ρ) *
          ∫ q, Φ (regenerationRecord hd lam l 0 q) ∂ν)) := by
  have hpath := ae_quenched_tubeEvent_mass_pos_of_killed_ae_pos hd
    Q.ellipticity_parameter Q lam h₀.le h₁ h₀ P hK.2.2.1
    (Renewal.forceCoord hd) l hl hstep
  have hmass := annealed_tubeEvent_mass_pos Q.measure K P hK.1 hK.2.1
    (Renewal.forceCoord hd) lam l hpath
  exact condition_iterate_of_tube_mass_pos hindep hd Q lam h₀ h₁ l δ hl
    hsep hδ hδ₁ P K hK hD hmass

end EndpointMass

open Regeneration

/-- The supplied tail statement produces the full condition-iterate conclusion
at every scale above its original construction threshold. No tube estimate or
extra graph premise is used. Smaller admissible scales remain a separate gap. -/
theorem condition_iterate_at_construction_scales
    (hindep : node_app_u3A_factorization_u23_independenceStmtV2)
    (htails : node_app_u3A_regen_u2D_tailsStmt)
    (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) :
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    let R := l / lam
    let i := Regeneration.Renewal.forceCoord hd
    let Δ := Regeneration.Renewal.regenDelta lam
    let μ := Regeneration.annealedCoupledLaw Q.measure K
    let ν := regenerationConditionedLaw hd Q lam l K
      hK.1 hD
    (∀ n : ℕ, 2 ≤ n → ∀ᵐ q ∂μ,
      EinsteinFull.regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) →
      (q ∈ regenerationNoReturn hd R ↔
        ∀ s : ℝ≥0, s ≤ (n - 1 : ℕ) * Δ → -R < q.2.1 s i)) ∧
    (∃ Θ : Regeneration.FutureState d i R → Regeneration.FutureState d i R,
      Measurable Θ ∧
      (∀ ρ ∈ ({μ, ν} : Set (Measure (FieldPair d × Regeneration.CoupledSample d))),
        ∀ k : ℕ, ∀ᵐ q ∂ρ,
          Θ (regenerationRecord hd lam l k q) = regenerationRecord hd lam l (k + 1) q) ∧
      Measure.map Θ (Measure.map (regenerationRecord hd lam l 0) ν) =
        Measure.map (regenerationRecord hd lam l 0) ν) ∧
    (∀ (Φ : Regeneration.FutureState d i R → ℝ),
      Measurable Φ → Regeneration.BoundedRealTest Φ →
      ∀ ρ ∈ ({μ, ν} : Set (Measure (FieldPair d × Regeneration.CoupledSample d))),
      (∀ k : ℕ, 1 ≤ k →
        (∫ q, Φ (regenerationRecord hd lam l k q) ∂ρ) =
          ∫ q, Φ (regenerationRecord hd lam l 0 q) ∂ν) ∧
      (∀ (F : FieldPair d → ℝ),
        Measurable[localSigma {x : Vec d | euclideanNorm x < R}] F →
        Regeneration.BoundedRealTest F →
        ∀ (n : ℕ), 2 ≤ n → ∀ (H : Regeneration.CoupledSample d → ℝ),
        Measurable[Regeneration.finiteHistorySigma Δ (n - 1)] H →
        Regeneration.BoundedRealTest H →
        (∫ q in {q | EinsteinFull.regenerationTime hd lam l 1 q.2 =
          (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)},
          F q.1 * H q.2 * Φ (regenerationRecord hd lam l 1 q) ∂ρ) =
        (∫ q in {q | EinsteinFull.regenerationTime hd lam l 1 q.2 =
          (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}, F q.1 * H q.2 ∂ρ) *
          ∫ q, Φ (regenerationRecord hd lam l 0 q) ∂ν)) := by
  obtain ⟨l₀, hl₀, hsep₀, ht⟩ := htails d hd Λ₀ r₀
  refine ⟨l₀, hl₀, hsep₀, ?_⟩
  intro l hscale δ hδ hδ₁ Q lam h₀ h₁ P K hK hD
  obtain ⟨_, _, a, _, _, _, _, _, _, hmom⟩ := ht l hscale δ hδ hδ₁
  obtain ⟨_, _, _, hm, _⟩ := hmom Q lam h₀ h₁ P K hK
  have hfin := Work.W5.regenerationTime_ne_top_ae_of_exponentialMoment hd
    lam l a 1 (annealedCoupledLaw Q.measure K)
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hm)
  simp only [EinsteinFull.regenerationTime, regenerationTime_one] at hfin
  have hsep : r₀ < 2 * l :=
    lt_of_lt_of_le hsep₀ (mul_le_mul_of_nonneg_left hscale (by norm_num))
  exact condition_iterate_of_first_finite hindep hd Q lam h₀ h₁ l δ
    (lt_of_lt_of_le hl₀ hscale) hsep hδ hδ₁ P K hK hD hfin

end
end EinsteinFull.Blueprint.FirstSlicePositivity

#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.continuous_euclideanNorm
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.meshPiece
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.meshPrefix
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.measurableSet_meshPiece
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.meshPrefix_zero
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.meshPrefix_succ
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.measurableSet_meshPrefix
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.meshPiece_congr
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.meshPrefix_prefix
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.measurableSet_meshPrefix_past
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.exists_mesh_interval
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.tubeCurve
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.continuous_tubeCurve
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.tubeEvent
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.measurableSet_tubeEvent
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.measurableSet_tubeEvent_history
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.euclideanNorm_unitVector
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.tubeCurve_dist_le
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.tubeCurve_mesh_dist
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.tubeStepTime
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.tubeCenters
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.coe_tubeStepTime
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.tubeStepTime_pos
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.tubeStepTime_total
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.tubeCenters_zero
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.tubeCenters_origin_mem
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.meshPrefix_subset_tubeEvent
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.meshPrefix_mass_succ
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.meshPrefix_endpoint_succ
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.meshPrefix_mass_step
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.meshPrefix_mass_lower
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.meshPrefix_mass_pos

#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.tubeEvent_mass_lower
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.ae_quenched_tubeEvent_mass_lower
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.annealed_tubeEvent_mass_lower
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.annealed_tubeEvent_fresh_bit_mass
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.annealed_tubeEvent_fresh_bit_pos

#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.tubeEvent_mem_forcedBitTrialEvent

#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.firstSlice_spatial_mass_factorization
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.endpointAverage_one
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.spatial_past_mass_eq
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.firstSlice_past_mass_factorization
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.firstTubeSlice
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.measurableSet_firstTubeSlice
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.firstTubeSlice_mass
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.firstTubeSlice_noReturn_ae
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.conditioned_firstTubeSlice_mass
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.conditioned_firstTubeSlice_pos_of_step_minorization
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.first_finite_of_step_minorization
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.tubeEvent_endpoint_coord_lt_four
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.endpointAverage_low_eq_zero
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.uniformSuccessfulEndpoint_zero_low_null
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.tubeEvent_bit_zero_false_ae
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.bit_zero_false_mass
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.tubeEvent_mass_eq_false_zero_cond
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.conditioned_firstTubeSlice_two_coin_mass
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.firstTubeSlice_two_coin_mass

#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.all_record_iteration_of_step_minorization

#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.condition_iterate_of_step_minorization

#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.meshPrefix_mass_pos_of_step_pos
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.tubeEvent_mass_pos_of_step_pos
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.ae_quenched_tubeEvent_mass_pos_of_step_pos
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.annealed_tubeEvent_mass_pos

#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.first_finite_of_tube_mass_pos
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.all_record_iteration_of_tube_mass_pos
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.condition_iterate_of_tube_mass_pos


#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.all_record_iteration_of_first_finite

#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.condition_iterate_of_first_finite

#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.condition_iterate_at_construction_scales

#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.meshBall
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.isOpen_meshBall
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.exists_pos_lt_killed_mass_ne_zero
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.killedEndpoint_mass_pos_of_ae_pos
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.meshPiece_mass_pos_of_killed_ae_pos

#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.tubeEvent_mass_pos_of_killed_ae_pos
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.tubeEvent_mass_pos_of_mesh_indicator_self

#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.meshBall_eq_unscaled
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.meshPiece_eq_unscaled
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.meshPiece_start
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.meshPiece_endpoint
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.meshPiece_zero
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.volume_meshBall
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.volume_meshBall_pos
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.killedEndpoint_meshBall_eq_meshPiece

#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.volume_meshBall_eq
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.meshPiece_mass_eq_restrict_map
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.meshPiece_mass_lower_of_killed_domination

#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.volume_meshTerminalBall
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.ae_meshPiece_mass_lower_of_killed_domination
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.ae_quenched_tubeEvent_mass_lower_of_killed_domination
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.tubeEvent_false_zero_cond_mass_lower_of_step_minorization
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.conditioned_firstTubeSlice_mass_lower_of_step_minorization
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.conditioned_firstTubeSlice_mass_lower_of_killed_domination

#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.conditioned_firstTubeSlice_pos_of_killed_domination

#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.killedEndpoint_mono_domain
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.killedEndpoint_mass_pos_eventually_at_zero
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.exists_pos_lt_killedEndpoint_mass_pos
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.killedEndpoint_mass_pos_of_positive_entrance

#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.meshTerminalBall_subset_domain
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.physicalReversibleMeasure_pos_iff_volume
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.physicalReversibleMeasure_meshTerminalBall_pos
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.meshTerminalBall_killed_mass_pos_eventually_at_zero

#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.ae_quenched_tubeEvent_mass_pos_of_killed_ae_pos
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.condition_iterate_of_killed_ae_pos

#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.physicalReversibleMeasure_restrict_ae_iff_volume

#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.killedL2_eq_zero_at_half
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.killedL2_eq_zero_iff
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.killedInteriorOperator_injective
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.killedL2_inner_pos

#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.h1_twoValue_rigidity

#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.memLp_restrict_volume_of_posDensity
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.weightedSobolevGraphH1Restrict
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.weightedSobolevGraph_twoValue_rigidity

#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.meshBall_eq_pdeEuclideanBall
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.meshBall_isOpenBoundedConvexDomain
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.physicalSobolev_twoValue_rigidity_meshBall
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.physicalSobolev_indicator_dichotomy_meshBall
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.killedFormBound_indicator_dichotomy_meshBall
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.physicalL2SupportProjection
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.physicalL2SupportProjection_ae_eq
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.physicalL2_inner_eq_zero_of_disjoint_support
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.killedFormDifferenceQuotient_supportProjection_le
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.invariantSupport_dichotomy_meshBall
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.invariantSupport_dichotomy_meshBall_of_closure_subset

#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.closure_meshBall_subset_of_lt
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.meshBall_eq_iUnion_inner
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.restrict_dichotomy_iUnion_of_common_core
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.invariantSupport_dichotomy_killing_meshBall

#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.killedL2_nonneg
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.killedL2_mono
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.killedL2_input_zero_on_of_zero_on
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.physicalReversibleMeasure_meshBall_ne_top
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.meshTerminalBall_killed_pos_ae_of_indicator_self
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.killedEndpoint_pos_ae_meshBall_of_indicator_self
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.killedL2_support_inclusion
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.killedL2_support_mono_time
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.killedL2_support_invariant_of_one_time
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.killedL2_positive_time_support_invariant_of_analytic
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.killedEndpoint_mass_pos_ae_on_target

#lint

#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.killedL2_zero_on_of_abs_le

#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.killedL2_zero_on_of_support
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.killedL2_support_invariant_of_self

#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.killedL2_support_dichotomy_killing_meshBall_of_self

#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.killedL2_pos_ae_killing_meshBall_of_self

#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.killedL2_second_increment_at_two_n_le

#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.killedL2_iterated_increment_at_n_le

#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.killedL2_mixed_increment_le

#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.killedL2_correlation_increment_nonneg

#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.killedL2_correlation_increment_polarized_le

#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.killedL2_linear_increment_at_n_le

#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.killedL2_iterated_linear_increment_at_n_le
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.killedL2_mixed_linear_increment_le

#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.killedL2_linear_increment_after_mesh_le
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.killedL2_linear_increment_at_time_le

#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.killedL2_linear_increment_positive_time_le
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.killedL2_linear_increment_all_steps_le
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.killedL2_iterated_linear_increment_all_steps_le
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.killedL2_second_increment_eq_iterate
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.killedL2_second_increment_bound
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.killedL2_adjacent_difference_quotients_bound
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.killedL2_dyadic_difference_quotients_converge
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.killedL2_dyadic_difference_quotients_converge_bound
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.killedL2_iterated_dyadic_quotients_converge
#print axioms EinsteinFull.Blueprint.FirstSlicePositivity.killedL2_iterated_linear_increment_positive_time_le
