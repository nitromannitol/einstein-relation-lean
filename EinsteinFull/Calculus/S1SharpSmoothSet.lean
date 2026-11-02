import EinsteinFull.Calculus.S1SharpAeSupport
import EinsteinFull.Calculus.S1SharpPhysicalBounds
import EinsteinFull.Calculus.S1SharpStructuralData
import EinsteinFull.Frozen.SmoothEnvironment

/-! A Borel set of field pairs, carrying the almost-sure smoothness bounds of the sharpness
example: every constructed physical pair lies in it, and every member satisfies
`IsSmoothWithBounds` for one derivative-bound sequence fixed before the noise sample
(`paper/main.tex:1534–1541`). -/

open MeasureTheory

namespace EinsteinFull.Calculus.S1

open EinsteinRelation EinsteinRelation.Sharpness EinsteinFull.Work.W8

variable {d : ℕ}

/-- The `(j, k)` entry of a matrix, as a continuous function. -/
def entryCM (d : ℕ) (j k : Fin d) : C(Mat d, ℝ) :=
  ⟨fun M => M j k, continuous_id.matrix_elem j k⟩

/-- The `(j, k)` entry of the matrix component, as a continuous function on space. -/
def entryMap (j k : Fin d) (ω : FieldPair d) : C(Vec d, ℝ) := (entryCM d j k).comp ω.1

theorem continuous_entryMap (j k : Fin d) : Continuous (entryMap (d := d) j k) :=
  (ContinuousMap.continuous_postcomp (entryCM d j k)).comp continuous_fst

/-- Field pairs whose entries and potential are smooth with prescribed bounds on all iterated
coordinate derivatives at the points of `D`. -/
def smoothBoundedPairs (D : Set (Vec d)) (C : List (Fin d) → ℝ) : Set (FieldPair d) :=
  {ω | ω.2 ∈ coordBoundSet D C ∧ ∀ j k, entryMap j k ω ∈ coordBoundSet D C}

theorem measurableSet_smoothBoundedPairs {D : Set (Vec d)} (hD : D.Countable)
    (C : List (Fin d) → ℝ) : MeasurableSet (smoothBoundedPairs D C) := by
  have h2 : MeasurableSet {ω : FieldPair d | ω.2 ∈ coordBoundSet D C} :=
    continuous_snd.measurable (measurableSet_coordBoundSet hD C)
  have h1 : ∀ j k : Fin d, MeasurableSet {ω : FieldPair d | entryMap j k ω ∈ coordBoundSet D C} :=
    fun j k => (continuous_entryMap j k).measurable (measurableSet_coordBoundSet hD C)
  have hset : smoothBoundedPairs D C = {ω : FieldPair d | ω.2 ∈ coordBoundSet D C} ∩
      ⋂ j : Fin d, ⋂ k : Fin d, {ω : FieldPair d | entryMap j k ω ∈ coordBoundSet D C} := by
    ext ω
    simp [smoothBoundedPairs]
  rw [hset]
  exact h2.inter (MeasurableSet.iInter fun j => MeasurableSet.iInter fun k => h1 j k)

/-- The operator-norm bound of order `k` for a sequence of coordinate bounds `C`. -/
noncomputable def Kc (C : List (Fin d) → ℝ) (k : ℕ) : ℝ :=
  ∑ dirs : Fin k → Fin d, |C (List.ofFn dirs)|

theorem Kc_nonneg (C : List (Fin d) → ℝ) (k : ℕ) : 0 ≤ Kc C k :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- The derivative-bound sequence of the structural data. -/
noncomputable def sharpDerivBound (d : ℕ) (C : List (Fin d) → ℝ) (k : ℕ) : ℝ :=
  d * d * Kc C k + Kc C k + 1

theorem abs_iteratedFDeriv_le_of_coordinate {f : Vec d → ℝ} (hs : ContDiff ℝ (⊤ : ℕ∞) f)
    (C : List (Fin d) → ℝ) (hC : ∀ l x, |iteratedCoordinateDerivative l f x| ≤ C l) (k : ℕ)
    (x : Vec d) (v : Fin k → Vec d) :
    |iteratedFDeriv ℝ k f x v| ≤ Kc C k * ∏ j, euclideanNorm (v j) := by
  rw [← Real.norm_eq_abs]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
  exact mul_le_mul (norm_iteratedFDeriv_le_of_coordinate hs C hC k x)
    (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun j _ => norm_le_euclideanNorm _))
    (Finset.prod_nonneg fun _ _ => norm_nonneg _) (Kc_nonneg C k)

theorem isSmoothWithBounds_of_mem {D : Set (Vec d)} (hD : Dense D) (C : List (Fin d) → ℝ)
    {ω : FieldPair d} (hω : ω ∈ smoothBoundedPairs D C) :
    IsSmoothWithBounds (sharpDerivBound d C) ω := by
  obtain ⟨h2, h1⟩ := hω
  refine ⟨⟨fun j k => (h1 j k).1, h2.1⟩, fun k _ => ⟨d * d * Kc C k, Kc C k, ?_, Kc_nonneg C k,
    ?_, ?_, ?_⟩⟩
  · exact mul_nonneg (by positivity) (Kc_nonneg C k)
  · show (d : ℝ) * d * Kc C k + Kc C k ≤ d * d * Kc C k + Kc C k + 1
    linarith
  · intro x v ξ
    set P : ℝ := ∏ j, euclideanNorm (v j) with hP
    have hP0 : 0 ≤ P := Finset.prod_nonneg fun j _ => Real.sqrt_nonneg _
    have hM : ∀ j l, |iteratedFDeriv ℝ k (fun y => ω.1 y j l) x v| ≤ Kc C k * P :=
      fun j l => abs_iteratedFDeriv_le_of_coordinate (f := fun y => ω.1 y j l) (h1 j l).1 C
        (fun l' x' => coordBoundSet_bound hD (h1 j l) l' x') k x v
    have hK0 := Kc_nonneg C k
    refine (euclideanNorm_le_sum_abs _).trans ?_
    have hξ : ∀ l, |ξ l| ≤ euclideanNorm ξ := fun l => abs_apply_le_euclideanNorm ξ l
    have hterm : ∀ j, |Matrix.mulVec (fun j l => iteratedFDeriv ℝ k
        (fun y => ω.1 y j l) x v) ξ j| ≤ d * (Kc C k * P * euclideanNorm ξ) := by
      intro j
      simp only [Matrix.mulVec, dotProduct]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ l, |iteratedFDeriv ℝ k (fun y => ω.1 y j l) x v * ξ l|
          ≤ ∑ _l : Fin d, Kc C k * P * euclideanNorm ξ := by
            apply Finset.sum_le_sum
            intro l _
            rw [abs_mul]
            exact mul_le_mul (hM j l) (hξ l) (abs_nonneg _) (mul_nonneg hK0 hP0)
        _ = d * (Kc C k * P * euclideanNorm ξ) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc ∑ j, |Matrix.mulVec (fun j l => iteratedFDeriv ℝ k
          (fun y => ω.1 y j l) x v) ξ j|
        ≤ ∑ _j : Fin d, (d : ℝ) * (Kc C k * P * euclideanNorm ξ) :=
          Finset.sum_le_sum fun j _ => hterm j
      _ = d * d * Kc C k * P * euclideanNorm ξ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  · intro x v
    exact abs_iteratedFDeriv_le_of_coordinate (f := fun y => ω.2 y) h2.1 C
      (fun l' x' => coordBoundSet_bound hD h2 l' x') k x v

/-- The structural data of the sharpness example, with the measurable carrier of the
almost-sure smoothness bounds. -/
theorem exists_sharpData (i : Fin d) :
    ∃ (D : StructuralData d) (S : Set (FieldPair d)), D.dependenceRange = 4 ∧
      4 ≤ D.ellipticity ∧
      (∀ W : NoiseSample d, IsRegular D.ellipticity (physicalPair i W)) ∧
      MeasurableSet S ∧ (∀ W : NoiseSample d, physicalPair i W ∈ S) ∧
      ∀ ω ∈ S, IsSmoothWithBounds D.derivativeBound ω := by
  obtain ⟨Λ, hΛ, hreg⟩ := exists_physicalPair_regularity i
  obtain ⟨Dn, hDn, hDd⟩ := TopologicalSpace.exists_countable_dense (Vec d)
  have hent : ∀ (l : List (Fin d)) (j k : Fin d), ∃ C : ℝ, ∀ (W : NoiseSample d) (x : Vec d),
      |iteratedCoordinateDerivative l (fun x => (physicalPair i W).1 x j k) x| ≤ C :=
    fun l j k => ((physicalPair_unifBdd i).2.2.1 j k).coordinate l
  have hpot : ∀ l : List (Fin d), ∃ C : ℝ, ∀ (W : NoiseSample d) (x : Vec d),
      |iteratedCoordinateDerivative l (fun x => (physicalPair i W).2 x) x| ≤ C :=
    fun l => (physicalPair_unifBdd i).2.2.2.coordinate l
  choose Ce hCe using hent
  choose Cp hCp using hpot
  let Cc : List (Fin d) → ℝ := fun l => (∑ j, ∑ k, |Ce l j k|) + |Cp l|
  have hCc : ∀ l, 0 ≤ ∑ j : Fin d, ∑ k : Fin d, |Ce l j k| := fun l =>
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => abs_nonneg _
  refine ⟨⟨Λ, 4, sharpDerivBound d Cc, by linarith, by norm_num, fun k _ => ?_⟩,
    smoothBoundedPairs Dn Cc, rfl, hΛ, hreg, measurableSet_smoothBoundedPairs hDn Cc, fun W => ?_,
    fun ω hω => isSmoothWithBounds_of_mem hDd Cc hω⟩
  · have := Kc_nonneg Cc k
    unfold sharpDerivBound
    positivity
  · obtain ⟨hsm1, hsm2⟩ := physicalPair_isSmooth i W
    refine ⟨⟨hsm2, fun l x _ => ?_⟩, fun j k => ⟨hsm1 j k, fun l x _ => ?_⟩⟩
    · refine (hCp l W x).trans ((le_abs_self _).trans ?_)
      show |Cp l| ≤ (∑ j : Fin d, ∑ k : Fin d, |Ce l j k|) + |Cp l|
      linarith [hCc l]
    · refine (hCe l j k W x).trans ((le_abs_self _).trans ?_)
      have h1 : |Ce l j k| ≤ ∑ k', |Ce l j k'| :=
        Finset.single_le_sum (f := fun k' => |Ce l j k'|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ k)
      have h2 : ∑ k', |Ce l j k'| ≤ ∑ j', ∑ k', |Ce l j' k'| :=
        Finset.single_le_sum (f := fun j' => ∑ k', |Ce l j' k'|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ j)
      show |Ce l j k| ≤ (∑ j', ∑ k', |Ce l j' k'|) + |Cp l|
      linarith [abs_nonneg (Cp l)]

end EinsteinFull.Calculus.S1
