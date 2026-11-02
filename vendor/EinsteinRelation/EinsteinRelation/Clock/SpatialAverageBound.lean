import EinsteinRelation.Clock.CentredClockField
import EinsteinRelation.Clock.HeatCubeDecomposition
import EinsteinRelation.Environment.LocalIntegralMeasurability
import EinsteinRelation.Environment.SeparatedIndependence
import EinsteinRelation.Probability.ColoredHoeffding
import EinsteinRelation.TimeChange.EuclideanTransport
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Spatial averages of the centred clock field

The heat-smoothed field `H_t f` of a bounded, centred, locally observed field `f` satisfies
`‖H_t f‖_{L^m(P)} ≤ C (1 + t) ^ (-d/4)` under a stationary law `P` of finite range
(`paper/main.tex:1155-1163`). The proof splits `f` into the pieces over the unit cubes of the
heat-kernel partition. Cubes are coloured by their indices modulo `N`, so that cubes of one colour
are more than `r₀` apart. Each colour class is independent, and the colour-class Hoeffding bound
`eLpNorm_tsum_le_colored` adds the classes. The centred clock density is a bounded field observed
at the origin, so it satisfies the hypotheses, and the scalar averaging estimate follows with a
constant that depends only on the dimension and the environment bounds, not on the law or on the
scale `R`.
-/

open MeasureTheory
open EinsteinRelation.Correctors (euclideanHeatKernel heatSmoothed)

namespace EinsteinRelation.Clock

/-! ### Euclidean geometry of the neighbourhoods of cubes -/

/-- The Euclidean norm is continuous on the coordinate space. -/
private theorem spatialNorm_continuous {d : ℕ} :
    Continuous fun v : Vec d => euclideanNorm v := by
  have hsum : Continuous fun v : Vec d => ∑ j, v j * v j :=
    continuous_finset_sum Finset.univ fun j _ => (continuous_apply j).mul (continuous_apply j)
  unfold euclideanNorm euclideanSq dot
  exact Real.continuous_sqrt.comp hsum

/-- The Euclidean norm does not change under negation. -/
private theorem euclideanNorm_neg_vec {d : ℕ} (v : Vec d) :
    euclideanNorm (-v) = euclideanNorm v := by
  unfold euclideanNorm euclideanSq dot
  simp only [Pi.neg_apply, neg_mul_neg]

/-- The Euclidean `r`-neighbourhood of the unit cube with index `z`. -/
noncomputable def clockNbhd {d : ℕ} (r : ℝ) (z : Fin d → ℤ) : Set (Vec d) :=
  ⋃ a ∈ heatCube 1 z, {p : Vec d | euclideanNorm (p - a) < r}

/-- Membership in the `r`-neighbourhood of a unit cube. -/
private theorem mem_clockNbhd_iff {d : ℕ} {r : ℝ} {z : Fin d → ℤ} {x : Vec d} :
    x ∈ clockNbhd r z ↔ ∃ a ∈ heatCube 1 z, euclideanNorm (x - a) < r := by
  unfold clockNbhd
  constructor
  · intro h
    obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.mp h
    exact ⟨a, ha, hxa⟩
  · rintro ⟨a, ha, hxa⟩
    exact Set.mem_iUnion₂.mpr ⟨a, ha, hxa⟩

/-- The `r`-neighbourhood of a unit cube is open. -/
private theorem isOpen_clockNbhd {d : ℕ} (r : ℝ) (z : Fin d → ℤ) :
    IsOpen (clockNbhd r z) := by
  unfold clockNbhd
  refine isOpen_biUnion fun a _ => ?_
  exact isOpen_lt ((spatialNorm_continuous (d := d)).comp (continuous_id.sub continuous_const))
    continuous_const

/-- Points of two unit cubes with equal colour, at distance `r` from their cubes, are at least
`N - 1 - 2 r` apart. The cubes are separated by `(N - 1)` (`heatCube_dist_of_same_colour`), and
each neighbourhood moves a point by less than `r`. -/
private theorem clockNbhd_separated {d : ℕ} {r : ℝ} (N : ℕ) {z w : Fin d → ℤ} (hzw : z ≠ w)
    (hcol : heatCubeColour N z = heatCubeColour N w) {x y : Vec d}
    (hx : x ∈ clockNbhd r z) (hy : y ∈ clockNbhd r w) :
    (N : ℝ) - 1 - 2 * r ≤ euclideanNorm (x - y) := by
  obtain ⟨a, ha, hxa⟩ := mem_clockNbhd_iff.mp hx
  obtain ⟨b, hb, hyb⟩ := mem_clockNbhd_iff.mp hy
  have hsep : ((N : ℝ) - 1) * 1 ≤ euclideanNorm (a - b) :=
    heatCube_dist_of_same_colour one_pos N hzw hcol a ha b hb
  rw [mul_one] at hsep
  have hneg : euclideanNorm (a - x) = euclideanNorm (x - a) := by
    have h := euclideanNorm_neg_vec (x - a)
    rwa [neg_sub] at h
  have e : a - b = (a - x) + (x - y) + (y - b) := by abel
  have htri1 := EinsteinRelation.TimeChange.euclideanNorm_add_le ((a - x) + (x - y)) (y - b)
  have htri2 := EinsteinRelation.TimeChange.euclideanNorm_add_le (a - x) (x - y)
  have htri : euclideanNorm (a - b) ≤
      euclideanNorm (a - x) + euclideanNorm (x - y) + euclideanNorm (y - b) := by
    rw [e]
    linarith
  linarith

/-! ### Measurability of the cube pieces -/

/-- The heat kernel is measurable. -/
private theorem clockKernel_measurable {d : ℕ} (t : ℝ) :
    Measurable fun x : Vec d => euclideanHeatKernel t x := by
  have hsq : Continuous fun x : Vec d => euclideanSq x := by
    unfold euclideanSq dot
    exact continuous_finset_sum Finset.univ fun i _ => (continuous_apply i).mul (continuous_apply i)
  have hc : Continuous fun x : Vec d => euclideanHeatKernel t x := by
    unfold euclideanHeatKernel
    exact continuous_const.mul (Real.continuous_exp.comp (hsq.neg.div_const (4 * t)))
  exact hc.measurable

/-- The contribution of the unit cube `z` to `H_t f` is measurable for the local σ-algebra of the
neighbourhood of that cube, when `f` is measurable for the local σ-algebra of the ball of radius
`r₁` about the origin. -/
private theorem measurable_clockPiece_localSigma {d : ℕ} {r₁ : ℝ} (t : ℝ) {f : FieldPair d → ℝ}
    (hfloc : Measurable[EinsteinRelation.localSigma
      {y : Vec d | euclideanNorm (y - (0 : Vec d)) < r₁}] f)
    (z : Fin d → ℤ) :
    Measurable[EinsteinRelation.localSigma (clockNbhd r₁ z)] (heatCubePiece 1 t f z) := by
  have hSW : ∀ x ∈ heatCube 1 z, ∀ y ∈ {y : Vec d | euclideanNorm (y - (0 : Vec d)) < r₁},
      x + y ∈ clockNbhd r₁ z := by
    intro x hx y hy
    have hy' : euclideanNorm (y - (0 : Vec d)) < r₁ := hy
    refine mem_clockNbhd_iff.mpr ⟨x, hx, ?_⟩
    rw [add_sub_cancel_left]
    rwa [sub_zero] at hy'
  exact EinsteinRelation.measurable_localSigma_setIntegral_translate
    (measurableSet_heatCube 1 z) hSW (fun x => euclideanHeatKernel t x)
    (clockKernel_measurable (d := d) t) f hfloc

/-! ### Colouring of the cubes -/

/-- The colour of the unit cube with index `z`: the residues of `z` modulo `N`, numbered by
`Fintype.equivFin`. Cubes of one colour are more than `r₀` apart when `N` is large. -/
noncomputable def clockColour {d : ℕ} (N : ℕ) [NeZero N] (z : Fin d → ℤ) :
    Fin (Fintype.card (Fin d → ZMod N)) :=
  Fintype.equivFin (Fin d → ZMod N) (heatCubeColour N z)

/-! ### Real-variable estimates -/

/-- The square root of a sum bounded by `A (1 + t) ^ (-d/2)` is bounded by
`A ^ (1/2) (1 + t) ^ (-d/4)`. -/
private theorem rpow_half_le_of_sq_le {A S t : ℝ} {d : ℕ} (ht : 0 ≤ t) (hA : 0 ≤ A)
    (hS0 : 0 ≤ S) (hS : S ≤ A * (1 + t) ^ (-(d : ℝ) / 2)) :
    S ^ (1 / 2 : ℝ) ≤ A ^ (1 / 2 : ℝ) * (1 + t) ^ (-(d : ℝ) / 4) := by
  have hpos : (0 : ℝ) ≤ 1 + t := by linarith
  have h1 : S ^ (1 / 2 : ℝ) ≤ (A * (1 + t) ^ (-(d : ℝ) / 2)) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow hS0 hS (by norm_num)
  rw [Real.mul_rpow hA (Real.rpow_nonneg hpos (-(d : ℝ) / 2)), ← Real.rpow_mul hpos] at h1
  have h2 : -(d : ℝ) / 2 * (1 / 2 : ℝ) = -(d : ℝ) / 4 := by ring
  rw [h2] at h1
  exact h1

/-- Combining the colour constant `a`, the square-root bound and the decay factor `p ≥ 0`. -/
private theorem heat_bound_arith {a b D p S : ℝ} (hS : 0 ≤ S) (hp : 0 ≤ p)
    (hroot : S ^ (1 / 2 : ℝ) ≤ D * p) :
    a * S ^ (1 / 2 : ℝ) ≤ (|a| * D + |b|) * p := by
  calc a * S ^ (1 / 2 : ℝ) ≤ |a| * S ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right (le_abs_self a) (Real.rpow_nonneg hS _)
    _ ≤ |a| * (D * p) := mul_le_mul_of_nonneg_left hroot (abs_nonneg a)
    _ = (|a| * D) * p := by ring
    _ ≤ (|a| * D) * p + |b| * p :=
        le_add_of_nonneg_right (mul_nonneg (abs_nonneg b) hp)
    _ = (|a| * D + |b|) * p := by ring

/-! ### Stationary laws and a.e. equality -/

/-- For a stationary law, `f = g` almost everywhere implies that for almost every environment
`ω`, the translates satisfy `f (T_x ω) = g (T_x ω)` for almost every shift `x`. -/
private theorem ae_translate_eq_of_ae_eq {d : ℕ} {P : Measure (FieldPair d)}
    [IsProbabilityMeasure P] (hP : IsStationary P) {f g : FieldPair d → ℝ} (hfg : f =ᵐ[P] g) :
    ∀ᵐ ω ∂P, ∀ᵐ x : Vec d, f (translate x ω) = g (translate x ω) := by
  have hae : P {ω | ¬ f ω = g ω} = 0 := ae_iff.mp hfg
  obtain ⟨M, hMmeas, hMnull, hsub⟩ : ∃ M : Set (FieldPair d), MeasurableSet M ∧ P M = 0 ∧
      {ω | ¬ f ω = g ω} ⊆ M :=
    ⟨toMeasurable P {ω | ¬ f ω = g ω}, measurableSet_toMeasurable _ _,
      by rw [measure_toMeasurable]; exact hae, subset_toMeasurable _ _⟩
  have hNmeas : MeasurableSet ((fun p : Vec d × FieldPair d => translate p.1 p.2) ⁻¹' M) :=
    (EinsteinRelation.Probability.continuous_translate (d := d)).measurable hMmeas
  have hslice : ∀ x : Vec d,
      P (Prod.mk x ⁻¹' ((fun p : Vec d × FieldPair d => translate p.1 p.2) ⁻¹' M)) = 0 := by
    intro x
    have hpre : Prod.mk x ⁻¹' ((fun p : Vec d × FieldPair d => translate p.1 p.2) ⁻¹' M) =
        translate x ⁻¹' M := rfl
    rw [hpre, ← Measure.map_apply (EinsteinRelation.Probability.measurable_translate x) hMmeas,
      hP x]
    exact hMnull
  have hNnull : ((volume : Measure (Vec d)).prod P)
      ((fun p : Vec d × FieldPair d => translate p.1 p.2) ⁻¹' M) = 0 := by
    rw [Measure.prod_apply hNmeas]
    simp only [hslice, lintegral_zero]
  have hTnull : (P.prod (volume : Measure (Vec d)))
      (Prod.swap ⁻¹' ((fun p : Vec d × FieldPair d => translate p.1 p.2) ⁻¹' M)) = 0 := by
    rw [← Measure.map_apply measurable_swap hNmeas, Measure.prod_swap]
    exact hNnull
  have hae_pair : ∀ᵐ z ∂(P.prod (volume : Measure (Vec d))),
      z ∉ Prod.swap ⁻¹' ((fun p : Vec d × FieldPair d => translate p.1 p.2) ⁻¹' M) :=
    measure_eq_zero_iff_ae_notMem.mp hTnull
  have hae_f : ∀ᵐ z ∂(P.prod (volume : Measure (Vec d))),
      f (translate z.2 z.1) = g (translate z.2 z.1) := by
    filter_upwards [hae_pair] with z hz
    by_contra hne
    exact hz (hsub (show translate z.2 z.1 ∈ {ω | ¬ f ω = g ω} from hne))
  exact Measure.ae_ae_of_ae_prod
    (p := fun z : FieldPair d × Vec d => f (translate z.2 z.1) = g (translate z.2 z.1)) hae_f

/-- **Heat smoothing respects almost-everywhere equality under stationary laws.** If `f = g`
almost surely under a stationary law `P`, then `H_t f = H_t g` almost surely, for every `t`. -/
theorem heatSmoothed_congr_ae {d : ℕ} (t : ℝ) {P : Measure (FieldPair d)}
    [IsProbabilityMeasure P] (hP : IsStationary P) {f g : FieldPair d → ℝ}
    (hfg : f =ᵐ[P] g) : heatSmoothed t f =ᵐ[P] heatSmoothed t g := by
  by_cases ht : t = 0
  · filter_upwards [hfg] with ω hω
    simp [heatSmoothed, ht, hω]
  · filter_upwards [ae_translate_eq_of_ae_eq hP hfg] with ω hω
    simp only [heatSmoothed, if_neg ht]
    refine integral_congr_ae ?_
    filter_upwards [hω] with x hx
    simp only [hx]

/-! ### The centred clock density -/

/-- The centred clock density is measurable for the local σ-algebra of the unit ball about the
origin, since the origin lies in that ball. -/
private theorem measurable_centredClock_localSigma_one {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) :
    Measurable[EinsteinRelation.localSigma {y : Vec d | euclideanNorm (y - (0 : Vec d)) < 1}]
      (centredClock Q) := by
  have h0 : (0 : Vec d) ∈ {y : Vec d | euclideanNorm (y - (0 : Vec d)) < 1} := by
    have h00 : euclideanNorm ((0 : Vec d) - (0 : Vec d)) = 0 := by
      simp [euclideanNorm, euclideanSq, dot]
    show euclideanNorm ((0 : Vec d) - (0 : Vec d)) < 1
    rw [h00]
    norm_num
  have h := (measurable_clockAtOrigin_localSigma h0).sub_const
    (∫ w, w.2 (0 : Vec d) ∂(Carriers.reducedReferenceLaw Q))
  exact h

/-! ### The local heat-smoothing bound -/

/-- **Spatial averages of a local bounded field.** Let `P` be a stationary probability law on
field pairs with joint finite range `r₀`. Let `f` be a bounded, measurable, centred field that is
measurable for the local σ-algebra of the ball of radius `r₁` about the origin. Then for every
`m ≥ 1` there is a constant `C`, depending only on `d`, `r₀`, `r₁`, `B` and `m` (not on `P`, `f`
or `t`), such that `‖H_t f‖_{L^m(P)} ≤ C (1 + t) ^ (-d/4)` for all `t ≥ 0`
(`paper/main.tex:1155-1163`). -/
theorem eLpNorm_heatSmoothed_local_le {d : ℕ} (r₀ r₁ B m : ℝ) (hr₁ : 0 ≤ r₁) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P : Measure (FieldPair d)) [IsProbabilityMeasure P],
      IsStationary P → HasFiniteRange r₀ P → ∀ f : FieldPair d → ℝ, Measurable f →
        Measurable[EinsteinRelation.localSigma {y : Vec d | euclideanNorm (y - (0 : Vec d)) < r₁}]
          f →
        (∀ ω, |f ω| ≤ B) → ∫ ω, f ω ∂P = 0 → ∀ t : ℝ, 0 ≤ t →
        eLpNorm (heatSmoothed t f) (ENNReal.ofReal m) P ≤
          ENNReal.ofReal (C * (1 + t) ^ (-(d : ℝ) / 4)) := by
  -- Choose `N` so that cubes of one colour are separated by more than `r₀`.
  obtain ⟨N, hN⟩ := exists_nat_gt (|r₀| + 2 * r₁ + 3)
  have hNpos : (0 : ℝ) < N := by linarith [abs_nonneg r₀]
  have hN0 : N ≠ 0 := by
    intro h
    rw [h, Nat.cast_zero] at hNpos
    exact lt_irrefl _ hNpos
  haveI : NeZero N := ⟨hN0⟩
  have hgap : r₀ < (N : ℝ) - 1 - 2 * r₁ := by linarith [le_abs_self r₀]
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_summable_sq_heatCubePiece_bound (d := d) (L := 1) one_pos B
  have hD0 : 0 ≤ (B ^ 2 * C₁) ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg (mul_nonneg (sq_nonneg B) hC₁0) _
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = |((Fintype.card (Fin d → ZMod N) : ℕ) : ℝ) *
      EinsteinRelation.Probability.hoeffdingMomentConst m ^ (1 / m)| *
        (B ^ 2 * C₁) ^ (1 / 2 : ℝ) + |B| := ⟨_, rfl⟩
  refine ⟨C, ?_, ?_⟩
  · rw [hC]
    exact add_nonneg (mul_nonneg (abs_nonneg _) hD0) (abs_nonneg _)
  intro P _ hstat hfin f hf hfloc hfB hmean t ht
  have hCB : |B| ≤ C := by
    rw [hC]
    exact le_add_of_nonneg_left (mul_nonneg (abs_nonneg _) hD0)
  rcases ht.eq_or_lt with h0 | hpos
  · -- At `t = 0` the smoothing is the identity, and `|f| ≤ B ≤ C`.
    subst h0
    have hfun0 : heatSmoothed 0 f = f := by
      funext ω
      simp [heatSmoothed]
    have hbt : ∀ᵐ ω ∂P, ‖f ω‖ ≤ C := ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]
      exact (hfB ω).trans (le_trans (le_abs_self B) hCB)
    have hfC : eLpNorm f (ENNReal.ofReal m) P ≤ ENNReal.ofReal C := by
      refine (eLpNorm_le_of_ae_bound hf.aestronglyMeasurable hbt).trans ?_
      simp
    rw [hfun0]
    simp only [add_zero, Real.one_rpow, mul_one]
    exact hfC
  · -- For `t > 0`, split `H_t f` over the cubes and colour the cube pieces.
    have hpiece := hasSum_heatCubePiece (d := d) (L := 1) (B := B) one_pos hpos hf hfB
    have hfun : heatSmoothed t f = fun ω => ∑' z : Fin d → ℤ, heatCubePiece 1 t f z ω :=
      funext fun ω => (hpiece ω).tsum_eq.symm
    obtain ⟨hsumm, hle⟩ := hC₁ t hpos
    have hmeasX : ∀ z : Fin d → ℤ, Measurable (heatCubePiece 1 t f z) := fun z =>
      (measurable_clockPiece_localSigma t hfloc z).mono
        (EinsteinRelation.Probability.localSigma_le_borel _) le_rfl
    have hcX : ∀ z : Fin d → ℤ, ∀ᵐ ω ∂P, |heatCubePiece 1 t f z ω| ≤ B * heatCubeMass 1 t z :=
      fun z => ae_of_all _ fun ω => abs_heatCubePiece_le (L := 1) hpos hfB z ω
    have hmeanX : ∀ z : Fin d → ℤ, ∫ ω, heatCubePiece 1 t f z ω ∂P = 0 :=
      fun z => integral_heatCubePiece_eq_zero (L := 1) hpos hf hfB hstat hmean z
    have hindep : ∀ (k : Fin (Fintype.card (Fin d → ZMod N))) (s : Finset (Fin d → ℤ)),
        (∀ i ∈ s, clockColour N i = k) →
          ProbabilityTheory.iIndepFun (fun i : s => heatCubePiece 1 t f (i : Fin d → ℤ)) P := by
      intro k s hs
      have hsep : ∀ i j : s, i ≠ j → ∀ x ∈ clockNbhd r₁ (i : Fin d → ℤ),
          ∀ y ∈ clockNbhd r₁ (j : Fin d → ℤ), (N : ℝ) - 1 - 2 * r₁ ≤ euclideanNorm (x - y) := by
        intro i j hij x hx y hy
        have hc : Fintype.equivFin (Fin d → ZMod N) (heatCubeColour N (i : Fin d → ℤ)) =
            Fintype.equivFin (Fin d → ZMod N) (heatCubeColour N (j : Fin d → ℤ)) :=
          (hs _ i.2).trans (hs _ j.2).symm
        have hzw : (i : Fin d → ℤ) ≠ (j : Fin d → ℤ) := fun h => hij (Subtype.ext h)
        exact clockNbhd_separated N hzw ((Fintype.equivFin (Fin d → ZMod N)).injective hc) hx hy
      exact EinsteinRelation.iIndepFun_of_separated P r₀ ((N : ℝ) - 1 - 2 * r₁) hgap hfin
        (fun i : s => clockNbhd r₁ (i : Fin d → ℤ))
        (fun i : s => (isOpen_clockNbhd r₁ (i : Fin d → ℤ)).measurableSet) hsep
        (fun i : s => heatCubePiece 1 t f (i : Fin d → ℤ))
        (fun i : s => measurable_clockPiece_localSigma t hfloc (i : Fin d → ℤ))
    have hcolour := EinsteinRelation.Probability.eLpNorm_tsum_le_colored (μ := P)
      (clockColour (d := d) N)
      (fun z => heatCubePiece 1 t f z) hmeasX (fun z => B * heatCubeMass 1 t z) hindep hcX hmeanX
      hsumm (fun ω => (hpiece ω).summable) m hm
    have hroot := rpow_half_le_of_sq_le (d := d) hpos.le
      (mul_nonneg (sq_nonneg B) hC₁0) (tsum_nonneg fun z => sq_nonneg (B * heatCubeMass 1 t z)) hle
    have hp : 0 ≤ (1 + t) ^ (-(d : ℝ) / 4) := Real.rpow_nonneg (by linarith) _
    rw [hfun, hC]
    refine hcolour.trans (ENNReal.ofReal_le_ofReal ?_)
    exact heat_bound_arith (tsum_nonneg fun z => sq_nonneg (B * heatCubeMass 1 t z)) hp hroot

/-! ### The clock field satisfies the scalar averaging assumption -/

/-- **Clock spatial averages.** For every dimension `d ≥ 2` and environment bounds `Λ₀`, `r₀`, there
is a family `M` of constants, independent of the environment law `Q` and of the scale `R`, such
that the centred clock density `μ - E μ` is a scalar averaging field at every scale `R > 0`
(`paper/main.tex:1155-1163`). -/
theorem exists_clock_averaging :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ), ∃ M : ℝ → ℝ, (∀ m, 0 ≤ M m) ∧
      ∀ (Q : EnvironmentLaw d Λ₀ r₀) (R : ℝ), 0 < R →
        Carriers.IsScalarAveragingField Q M R (centredClock Q) := by
  intro d hd Λ₀ r₀
  have key : ∀ m : ℝ, 1 ≤ m → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (P : Measure (FieldPair d)) [IsProbabilityMeasure P],
        IsStationary P → HasFiniteRange r₀ P → ∀ f : FieldPair d → ℝ, Measurable f →
          Measurable[EinsteinRelation.localSigma {y : Vec d | euclideanNorm (y - (0 : Vec d)) < 1}]
            f →
          (∀ ω, |f ω| ≤ 2 * sourceReducedBound Λ₀) → ∫ ω, f ω ∂P = 0 → ∀ t : ℝ, 0 ≤ t →
          eLpNorm (heatSmoothed t f) (ENNReal.ofReal m) P ≤
            ENNReal.ofReal (C * (1 + t) ^ (-(d : ℝ) / 4)) :=
    fun m hm => eLpNorm_heatSmoothed_local_le r₀ 1 (2 * sourceReducedBound Λ₀) m zero_le_one hm
  choose! Cm _ hCm using key
  refine ⟨fun m => |Cm m|, fun m => abs_nonneg _, fun Q R hR => ?_⟩
  haveI := isProbabilityMeasure_reducedReferenceLaw Q
  have hB0 : 0 ≤ 2 * sourceReducedBound Λ₀ := by
    have := sourceReducedBound_pos Q.ellipticity_parameter
    linarith
  -- Truncating the centred clock density at `±2 Λ` does not change it almost surely.
  have hfae : centredClock Q =ᵐ[Carriers.reducedReferenceLaw Q]
      (fun w => max (-(2 * sourceReducedBound Λ₀))
        (min (2 * sourceReducedBound Λ₀) (centredClock Q w))) := by
    filter_upwards [abs_centredClock_le Q] with w hw
    obtain ⟨h1, h2⟩ := abs_le.mp hw
    show centredClock Q w = max (-(2 * sourceReducedBound Λ₀))
      (min (2 * sourceReducedBound Λ₀) (centredClock Q w))
    rw [min_eq_right h2, max_eq_right h1]
  have hfbound : ∀ w : FieldPair d,
      |max (-(2 * sourceReducedBound Λ₀)) (min (2 * sourceReducedBound Λ₀) (centredClock Q w))|
        ≤ 2 * sourceReducedBound Λ₀ := by
    intro w
    rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have hcc : Measurable (centredClock Q) := by
    have h := (continuous_clockAtOrigin (d := d)).measurable.sub_const
      (∫ w, w.2 (0 : Vec d) ∂(Carriers.reducedReferenceLaw Q))
    exact h
  have hφ : Measurable (fun s : ℝ =>
      max (-(2 * sourceReducedBound Λ₀)) (min (2 * sourceReducedBound Λ₀) s)) :=
    measurable_const.max (measurable_const.min measurable_id)
  have hfmeas : Measurable (fun w : FieldPair d =>
      max (-(2 * sourceReducedBound Λ₀)) (min (2 * sourceReducedBound Λ₀) (centredClock Q w))) :=
    hφ.comp hcc
  have hfloc : Measurable[EinsteinRelation.localSigma
      {y : Vec d | euclideanNorm (y - (0 : Vec d)) < 1}] (fun w : FieldPair d =>
      max (-(2 * sourceReducedBound Λ₀)) (min (2 * sourceReducedBound Λ₀) (centredClock Q w))) :=
    hφ.comp (measurable_centredClock_localSigma_one Q)
  have hmean : ∫ w, max (-(2 * sourceReducedBound Λ₀))
      (min (2 * sourceReducedBound Λ₀) (centredClock Q w)) ∂(Carriers.reducedReferenceLaw Q) = 0 :=
    (integral_congr_ae hfae).symm.trans (integral_centredClock Q)
  refine isScalarAveragingField_of_heat_bound Q (fun m => |Cm m|) hR
    (measurable_centredClock_localSigma Q hR) (fun m _ => abs_nonneg _) ?_
  intro m hm t ht
  have hbound := hCm m (by linarith) (Carriers.reducedReferenceLaw Q)
    (isStationary_reducedReferenceLaw Q) (hasFiniteRange_reducedReferenceLaw Q) _ hfmeas hfloc
    hfbound hmean t ht
  refine (eLpNorm_congr_ae
    (heatSmoothed_congr_ae t (isStationary_reducedReferenceLaw Q) hfae)).trans_le
    (hbound.trans ?_)
  apply ENNReal.ofReal_le_ofReal
  have hp : 0 ≤ (1 + t) ^ (-(d : ℝ) / 4) := Real.rpow_nonneg (by linarith) _
  calc Cm m * (1 + t) ^ (-(d : ℝ) / 4) ≤ |Cm m| * (1 + t) ^ (-(d : ℝ) / 4) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hp
    _ ≤ |Cm m| * (1 + t) ^ (-(1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (rpow_decay_le hd ht) (abs_nonneg _)

end EinsteinRelation.Clock
