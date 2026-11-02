import EinsteinFull.Calculus.S1SharpSmoothSet

/-! Structural data and a Borel carrier of smoothness bounds for an arbitrary family of regular
smooth field pairs with uniform derivative bounds (`paper/main.tex:1534–1541, 1565`). -/

open MeasureTheory

namespace EinsteinFull.Calculus.S1

open EinsteinRelation EinsteinRelation.Sharpness

variable {d : ℕ}

theorem exists_data_of_family {ι : Type*} (G : ι → FieldPair d)
    (hent : ∀ j k : Fin d, UnifBdd (fun (W : ι) x => (G W).1 x j k))
    (hpot : UnifBdd (fun (W : ι) x => (G W).2 x))
    (hsm : ∀ W, IsSmoothFieldPair (G W)) {Λ r : ℝ} (hΛ : 1 ≤ Λ) (hr : 1 ≤ r)
    (hreg : ∀ W, IsRegular Λ (G W)) :
    ∃ (D : StructuralData d) (S : Set (FieldPair d)), D.dependenceRange = r ∧
      D.ellipticity = Λ ∧ (∀ W, IsRegular D.ellipticity (G W)) ∧
      MeasurableSet S ∧ (∀ W, G W ∈ S) ∧
      ∀ ω ∈ S, IsSmoothWithBounds D.derivativeBound ω := by
  obtain ⟨Dn, hDn, hDd⟩ := TopologicalSpace.exists_countable_dense (Vec d)
  have hent' : ∀ (l : List (Fin d)) (j k : Fin d), ∃ C : ℝ, ∀ (W : ι) (x : Vec d),
      |iteratedCoordinateDerivative l (fun x => (G W).1 x j k) x| ≤ C :=
    fun l j k => (hent j k).coordinate l
  have hpot' : ∀ l : List (Fin d), ∃ C : ℝ, ∀ (W : ι) (x : Vec d),
      |iteratedCoordinateDerivative l (fun x => (G W).2 x) x| ≤ C :=
    fun l => hpot.coordinate l
  choose Ce hCe using hent'
  choose Cp hCp using hpot'
  let Cc : List (Fin d) → ℝ := fun l => (∑ j, ∑ k, |Ce l j k|) + |Cp l|
  have hCc : ∀ l, 0 ≤ ∑ j : Fin d, ∑ k : Fin d, |Ce l j k| := fun l =>
    Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => abs_nonneg _
  refine ⟨⟨Λ, r, sharpDerivBound d Cc, hΛ, hr, fun k _ => ?_⟩,
    smoothBoundedPairs Dn Cc, rfl, rfl, hreg, measurableSet_smoothBoundedPairs hDn Cc,
    fun W => ?_, fun ω hω => isSmoothWithBounds_of_mem hDd Cc hω⟩
  · have := Kc_nonneg Cc k
    unfold sharpDerivBound
    positivity
  · obtain ⟨hsm1, hsm2⟩ := hsm W
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
