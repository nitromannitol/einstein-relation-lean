import EinsteinFull.Homogenization.SourceResponseBridge
import Homogenization.Book.Ch02.Theorems.SymmetricDirichletNeumann

/-!
# Dual energy for source coefficients

The dual subadditive quantity in Armstrong, Kuusi and Mourrat, *Quantitative
Stochastic Homogenization and Large-Scale Regularity*, (2.1), is the supremum
of the Neumann energy over unrestricted Sobolev functions.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport

/-- The Neumann energy of a Sobolev function for the original coefficient. -/
noncomputable def sourceDualEnergyValue {d : ℕ} {K : ℝ} (a : Coefficient d K)
    (U : Book.Ch02.Domain d) (q : Vec d) (u : H1Function (U : Set (Vec d))) : ℝ :=
  Book.Ch02.average U fun x =>
    vecDot q (u.grad x) - (1 / 2 : ℝ) * vecDot (u.grad x) ((a x).mulVec (u.grad x))

/-- The admissible values in the definition of the dual energy. -/
noncomputable def sourceDualEnergyValueSet {d : ℕ} {K : ℝ} (a : Coefficient d K)
    (U : Book.Ch02.Domain d) (q : Vec d) : Set ℝ :=
  {E | ∃ u : H1Function (U : Set (Vec d)), E = sourceDualEnergyValue a U q u}

/-- The dual energy, defined using the original coefficient field. -/
noncomputable def sourceDualEnergy {d : ℕ} {K : ℝ} (a : Coefficient d K)
    (U : Book.Ch02.Domain d) (q : Vec d) : ℝ :=
  sSup (sourceDualEnergyValueSet a U q)

/-- The measurable representative is symmetric almost everywhere. -/
theorem sourceCoeffOn_isSymmetric {d : ℕ} {K : ℝ} (a : Coefficient d K)
    (U : Book.Ch02.Domain d) (k : ℕ) (hK : K ≤ (k : ℝ) + 1) :
    Book.Ch02.CoeffOn.IsSymmetric (sourceCoeffOn a U k hK) := by
  filter_upwards [ae_restrict_of_ae (regularCoefficient_ae_eq a)] with x hx
  change ((regularCoefficient a).toFun x).IsSymm
  rw [hx]
  exact a.symmetric x

/-- The original and regularized Neumann energies agree for every competitor. -/
theorem sourceDualEnergyValue_eq {d : ℕ} {K : ℝ} (a : Coefficient d K)
    (U : Book.Ch02.Domain d) (k : ℕ) (hK : K ≤ (k : ℝ) + 1)
    (q : Vec d) (u : H1Function (U : Set (Vec d))) :
    sourceDualEnergyValue a U q u =
      Book.Ch02.symmetricNeumannEnergyValue U (sourceCoeffOn a U k hK) q u := by
  unfold sourceDualEnergyValue Book.Ch02.symmetricNeumannEnergyValue Book.Ch02.average
  congr 1
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (regularCoefficient_ae_eq a)] with x hx
  simp only [sourceCoeffOn, hx]
  rfl

/-- The unrestricted Neumann variational problems have the same value set. -/
theorem sourceDualEnergyValueSet_eq {d : ℕ} {K : ℝ} (a : Coefficient d K)
    (U : Book.Ch02.Domain d) (k : ℕ) (hK : K ≤ (k : ℝ) + 1) (q : Vec d) :
    sourceDualEnergyValueSet a U q =
      Book.Ch02.symmetricNeumannValueSet U (sourceCoeffOn a U k hK) q := by
  ext E
  simp only [sourceDualEnergyValueSet, Book.Ch02.symmetricNeumannValueSet, Set.mem_ofPred_eq]
  simp only [sourceDualEnergyValue_eq a U k hK]

/-- The dual energy agrees with the symmetric Neumann variational value. -/
theorem sourceDualEnergy_eq {d : ℕ} {K : ℝ} (a : Coefficient d K)
    (U : Book.Ch02.Domain d) (k : ℕ) (hK : K ≤ (k : ℝ) + 1) (q : Vec d) :
    sourceDualEnergy a U q =
      Book.Ch02.symmetricNeumannNu U (sourceCoeffOn a U k hK) q := by
  unfold sourceDualEnergy Book.Ch02.symmetricNeumannNu
  rw [sourceDualEnergyValueSet_eq a U k hK]

/-- The integrand of every unrestricted dual competitor is integrable. -/
theorem integrableOn_sourceDualEnergyDensity {d : ℕ} {K : ℝ} (a : Coefficient d K)
    (U : Book.Ch02.Domain d) (k : ℕ) (hK : K ≤ (k : ℝ) + 1)
    (q : Vec d) (u : H1Function (U : Set (Vec d))) :
    IntegrableOn (fun x => vecDot q (u.grad x) -
      (1 / 2 : ℝ) * vecDot (u.grad x) ((a x).mulVec (u.grad x))) U := by
  let : IsFiniteMeasure (volumeMeasureOn (U : Set (Vec d))) :=
    Book.Ch02.Domain.instIsFiniteMeasureVolumeMeasureOn U
  have hEll := regularCoefficient_aeeQuantitativeEllipticSlice (U : Set (Vec d))
    U.measurableSet k hK a
  have hflux := hEll.memVectorL2_matVecMul u.grad_memVectorL2
  have hlinear := integrableOn_vecDot_of_memVectorL2 (memLp_const q) u.grad_memVectorL2
  have hquadratic := (integrableOn_vecDot_of_memVectorL2 u.grad_memVectorL2 hflux).const_mul
    (1 / 2 : ℝ)
  apply (hlinear.sub hquadratic).congr
  filter_upwards [ae_restrict_of_ae (regularCoefficient_ae_eq a)] with x hx
  change vecDot q (u.grad x) - (1 / 2 : ℝ) *
    vecDot (u.grad x) (matVecMul ((regularCoefficient a).toFun x) (u.grad x)) = _
  rw [hx]
  rfl

/-- The dual-energy value set is bounded above and has a maximizer. -/
theorem sourceDualEnergy_maximizer {d : ℕ} {K : ℝ} (a : Coefficient d K)
    (U : Book.Ch02.Domain d) (k : ℕ) (hK : K ≤ (k : ℝ) + 1) (q : Vec d) :
    ∃ u : H1Function (U : Set (Vec d)),
      (∀ v, sourceDualEnergyValue a U q v ≤ sourceDualEnergyValue a U q u) ∧
      sourceDualEnergy a U q = sourceDualEnergyValue a U q u := by
  let A := sourceCoeffOn a U k hK
  obtain ⟨u, _, hu⟩ := (Book.Ch02.responseSymmetricDirichletNeumannTheory U A
    (sourceCoeffOn_isSymmetric a U k hK)).neumann_meanZero_maximizer_exists q
  have hmax : ∀ v, sourceDualEnergyValue a U q v ≤ sourceDualEnergyValue a U q u := by
    intro v
    simpa only [sourceDualEnergyValue_eq a U k hK] using hu v
  refine ⟨u, hmax, ?_⟩
  apply le_antisymm
  · exact csSup_le ⟨sourceDualEnergyValue a U q u, u, rfl⟩ (by
      rintro E ⟨v, rfl⟩
      exact hmax v)
  · exact le_csSup ⟨sourceDualEnergyValue a U q u, by
      rintro E ⟨v, rfl⟩
      exact hmax v⟩ ⟨u, rfl⟩

/-- The supremum defining dual energy is taken over a bounded nonempty set. -/
theorem sourceDualEnergyValueSet_bddAbove {d : ℕ} {K : ℝ} (a : Coefficient d K)
    (U : Book.Ch02.Domain d) (k : ℕ) (hK : K ≤ (k : ℝ) + 1) (q : Vec d) :
    BddAbove (sourceDualEnergyValueSet a U q) := by
  obtain ⟨u, hu, _⟩ := sourceDualEnergy_maximizer a U k hK q
  exact ⟨sourceDualEnergyValue a U q u, by rintro E ⟨v, rfl⟩; exact hu v⟩

/-- The response splits into source Dirichlet and dual energies. -/
theorem responseJ_eq_sourceDirichlet_add_sourceDual {d : ℕ} {K : ℝ}
    (a : Coefficient d K) (U : Book.Ch02.Domain d) (k : ℕ)
    (hK : K ≤ (k : ℝ) + 1) (p q : Vec d) :
    Book.Ch02.responseJ U (sourceCoeffOn a U k hK) p q =
      EinsteinRelation.External.AKM.sourceDirichletEnergy a (U : Set (Vec d)) (-p) +
        sourceDualEnergy a U q - vecDot p q := by
  let A := sourceCoeffOn a U k hK
  let T := Book.Ch02.responseSymmetricDirichletNeumannTheory U A
    (sourceCoeffOn_isSymmetric a U k hK)
  have hzero : Book.Ch02.symmetricNeumannNu U A 0 = 0 := by
    rw [T.neumann_value_by_sigmaStarInv]
    simp [vecDot, matVecMul]
  have hdir : Book.Ch02.symmetricDirichletNu U A p =
      EinsteinRelation.External.AKM.sourceDirichletEnergy a (U : Set (Vec d)) (-p) := by
    have h := T.response_dirichlet_neumann_split p 0
    rw [hzero] at h
    simp only [vecDot, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, sub_zero] at h
    rw [sourceDirichletEnergy_eq_ResponseJ a U k hK (-p)]
    simpa only [neg_neg, ← Internal.Ch02.book_responseJ_eq_ResponseJ] using h.symm
  rw [T.response_dirichlet_neumann_split, hdir, sourceDualEnergy_eq a U k hK]

end EinsteinFull.Homogenization
