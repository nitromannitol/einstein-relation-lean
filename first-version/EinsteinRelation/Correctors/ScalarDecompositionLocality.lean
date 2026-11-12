import EinsteinRelation.Correctors.ScalarCorrectedWeakIdentities
import EinsteinRelation.Environment.LocalIntegralMeasurability

/-! # Locality of the explicit scalar decomposition

Source: `paper/main.tex:1048–1090`. The corrected band, its weak gradient,
the error flux, the drift flux and the drift remainder are measurable for
any common local observation window containing the origin. Their finite
sums preserve that same window.
-/

open MeasureTheory
open scoped Matrix

noncomputable section

namespace EinsteinRelation.Correctors

variable {d : ℕ}

/-- The coefficient at the origin is measurable on any observation window
containing the origin (`paper/main.tex:1088–1090`). -/
theorem measurable_coefficient_zero_localSigma {U : Set (Vec d)} (h0 : (0 : Vec d) ∈ U) :
    Measurable[localSigma U] (fun ω : FieldPair d => ω.1 0) := by
  have hpair : Measurable[localSigma U] (fun ω : FieldPair d => (ω.1 0, ω.2 0)) := by
    refine Measurable.of_comap_le ?_
    unfold localSigma
    exact le_iSup_of_le (⟨0, h0⟩ : U) le_rfl
  exact measurable_fst.comp hpair

private theorem measurable_mulVec {Ω : Type*} {m : MeasurableSpace Ω}
    {A : Ω → Mat d} {v : Ω → Vec d} (hA : Measurable[m] A) (hv : Measurable[m] v) :
    Measurable[m] (fun ω => A ω *ᵥ v ω) := by
  refine measurable_pi_iff.mpr fun i => ?_
  change Measurable[m] (fun ω => ∑ j, A ω i j * v ω j)
  exact Finset.measurable_sum _ fun j _ =>
    (((continuous_id : Continuous (fun M : Mat d => M)).matrix_elem i j).measurable.comp hA).mul
      ((measurable_pi_apply j).comp hv)

private theorem measurable_row {Ω : Type*} {m : MeasurableSpace Ω}
    {A : Ω → Mat d} (hA : Measurable[m] A) (i : Fin d) :
    Measurable[m] (fun ω k => A ω i k) := by
  refine measurable_pi_iff.mpr fun k => ?_
  exact ((continuous_id : Continuous (fun M : Mat d => M)).matrix_elem i k).measurable.comp hA

private theorem measurable_dot {Ω : Type*} {m : MeasurableSpace Ω}
    {v w : Ω → Vec d} (hv : Measurable[m] v) (hw : Measurable[m] w) :
    Measurable[m] (fun ω => dot (v ω) (w ω)) := by
  exact Finset.measurable_sum _ fun i _ =>
    ((measurable_pi_apply i).comp hv).mul ((measurable_pi_apply i).comp hw)

/-- All five corrected fields on one scale use the common observation
window of the band and the local correctors (`paper/main.tex:1048–1069`). -/
theorem measurable_localSigma_scalarCorrected {U : Set (Vec d)}
    (h0 : (0 : Vec d) ∈ U) (abar : Mat d) (i : Fin d)
    {u : FieldPair d → ℝ} {Du : FieldPair d → Vec d}
    {phi : Fin d → FieldPair d → ℝ} {Dphi DDu F : Fin d → FieldPair d → Vec d}
    {Sig : Fin d → FieldPair d → Mat d}
    (hu : Measurable[localSigma U] u) (hDu : Measurable[localSigma U] Du)
    (hphi : ∀ j, Measurable[localSigma U] (phi j))
    (hDphi : ∀ j, Measurable[localSigma U] (Dphi j))
    (hDDu : ∀ j, Measurable[localSigma U] (DDu j))
    (hF : ∀ j, Measurable[localSigma U] (F j))
    (hSig : ∀ j, Measurable[localSigma U] (Sig j)) :
    Measurable[localSigma U] (fun ω => u ω + ∑ j, phi j ω * Du ω j) ∧
    Measurable[localSigma U]
      (fun ω => Du ω + ∑ j, (Du ω j • Dphi j ω + phi j ω • DDu j ω)) ∧
    Measurable[localSigma U]
      (fun ω => ∑ j, (phi j ω • ((ω.1 0) *ᵥ DDu j ω) -
        Sig j ω *ᵥ DDu j ω + Du ω j • F j ω)) ∧
    Measurable[localSigma U]
      (fun ω => u ω • (abar *ᵥ unitVector i) + ∑ j, Du ω j • (fun k => Sig j ω i k)) ∧
    Measurable[localSigma U]
      (fun ω => ∑ j, (phi j ω * dot ((ω.1 0) *ᵥ unitVector i) (DDu j ω) -
        (Sig j ω *ᵥ DDu j ω) i + Du ω j * F j ω i)) := by
  have hDuj (j : Fin d) : Measurable[localSigma U] (fun ω => Du ω j) :=
    (measurable_pi_apply j).comp hDu
  have hA := measurable_coefficient_zero_localSigma h0
  have hAe : Measurable[localSigma U]
      (fun ω : FieldPair d => (ω.1 0) *ᵥ unitVector i) :=
    measurable_mulVec hA measurable_const
  have hrow (j : Fin d) : Measurable[localSigma U] (fun ω k => Sig j ω i k) :=
    measurable_row (hSig j) i
  refine ⟨hu.add (Finset.measurable_sum _ fun j _ => (hphi j).mul (hDuj j)),
    hDu.add (Finset.measurable_sum _ fun j _ =>
      ((hDuj j).smul (hDphi j)).add ((hphi j).smul (hDDu j))),
    Finset.measurable_sum _ (fun j _ => ?_),
    (hu.smul measurable_const).add (Finset.measurable_sum _ fun j _ => ?_),
    Finset.measurable_sum _ (fun j _ => ?_)⟩
  · exact (((hphi j).smul (measurable_mulVec hA (hDDu j))).sub
      (measurable_mulVec (hSig j) (hDDu j))).add ((hDuj j).smul (hF j))
  · exact (hDuj j).smul (hrow j)
  · exact (((hphi j).mul (measurable_dot hAe (hDDu j))).sub
      ((measurable_pi_apply i).comp (measurable_mulVec (hSig j) (hDDu j)))).add
      ((hDuj j).mul ((measurable_pi_apply i).comp (hF j)))

/-- The seven local measurability conclusions in `DecompositionConstruction`
follow for the literal global sums (`paper/main.tex:1088–1090`). -/
theorem measurable_localSigma_globalBands {ι : Type*} (s : Finset ι)
    {U : Set (Vec d)} {ψ h : ι → FieldPair d → ℝ}
    {Dψ B P : ι → FieldPair d → Vec d} {f e : FieldPair d → ℝ}
    {E₀ : FieldPair d → Vec d}
    (hψ : ∀ k ∈ s, Measurable[localSigma U] (ψ k))
    (hh : ∀ k ∈ s, Measurable[localSigma U] (h k))
    (hDψ : ∀ k ∈ s, Measurable[localSigma U] (Dψ k))
    (hB : ∀ k ∈ s, Measurable[localSigma U] (B k))
    (hP : ∀ k ∈ s, Measurable[localSigma U] (P k))
    (hf : Measurable[localSigma U] f) (he : Measurable[localSigma U] e)
    (hE₀ : Measurable[localSigma U] E₀) :
    Measurable[localSigma U] (fun ω => ∑ k ∈ s, ψ k ω) ∧
    Measurable[localSigma U] (fun ω => ∑ k ∈ s, h k ω) ∧
    Measurable[localSigma U] e ∧
    Measurable[localSigma U] (fun ω => E₀ ω - ∑ k ∈ s, B k ω) ∧
    Measurable[localSigma U] (fun ω => ∑ k ∈ s, P k ω) ∧
    Measurable[localSigma U] (fun ω => ∑ k ∈ s, Dψ k ω) ∧
    Measurable[localSigma U] (fun ω => f ω - e ω) :=
  ⟨Finset.measurable_sum s hψ, Finset.measurable_sum s hh, he,
    hE₀.sub (Finset.measurable_sum s hB), Finset.measurable_sum s hP,
    Finset.measurable_sum s hDψ, hf.sub he⟩

end EinsteinRelation.Correctors
