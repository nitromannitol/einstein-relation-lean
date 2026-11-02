import EinsteinFull.Frozen.SchwartzTestNorm
import EinsteinRelation.Environment.EuclideanLipschitz

namespace EinsteinFull
open EinsteinRelation

 theorem schwartzTestNorm_set_nonempty {d : ℕ} (N : ℕ)
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) :
    Set.Nonempty {q : ℝ | ∃ k : Fin (N + 1), ∃ dirs : Fin k.val → Fin d, ∃ x : Vec d,
      q = (1 + euclideanNorm x) ^ N *
        ‖iteratedFDeriv ℝ k.val (fun y => F y) x (fun j => unitVector (dirs j))‖} := by
  exact ⟨_, ⟨⟨0, by omega⟩, Fin.elim0, 0, rfl⟩⟩

 theorem schwartzTestNorm_set_bddAbove {d : ℕ} (N : ℕ)
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) :
    BddAbove {q : ℝ | ∃ k : Fin (N + 1), ∃ dirs : Fin k.val → Fin d, ∃ x : Vec d,
      q = (1 + euclideanNorm x) ^ N *
        ‖iteratedFDeriv ℝ k.val (fun y => F y) x (fun j => unitVector (dirs j))‖} := by
  refine ⟨((d : ℝ) + 1) ^ N *
    (2 ^ N * (Finset.Iic (N,N)).sup
      (fun m => SchwartzMap.seminorm ℝ m.1 m.2) F), ?_⟩
  rintro q ⟨k, dirs, x, rfl⟩
  have hpartial :
      ‖iteratedFDeriv ℝ k.val (fun y => F y) x (fun j => unitVector (dirs j))‖ ≤
      ‖iteratedFDeriv ℝ k.val (fun y => F y) x‖ := by
    simpa only [unitVector, Pi.norm_single, norm_one, Finset.prod_const_one, mul_one]
      using (iteratedFDeriv ℝ k.val (fun y => F y) x).le_opNorm
        (fun j => unitVector (dirs j))
  have hw : 1 + euclideanNorm x ≤ ((d : ℝ) + 1) * (1 + ‖x‖) := by
    have he := euclideanNorm_le_dimension_mul_norm x
    nlinarith only [he, Nat.cast_nonneg (α := ℝ) d]
  calc
    _ ≤ (((d : ℝ) + 1) * (1 + ‖x‖)) ^ N *
        ‖iteratedFDeriv ℝ k.val (fun y => F y) x‖ := by
      gcongr
      exact add_nonneg zero_le_one (Real.sqrt_nonneg _)
    _ = ((d : ℝ) + 1) ^ N * ((1 + ‖x‖) ^ N *
        ‖iteratedFDeriv ℝ k.val (fun y => F y) x‖) := by rw [mul_pow, mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (SchwartzMap.one_add_le_sup_seminorm_apply (m := (N,N)) le_rfl
        (Nat.le_of_lt_succ k.isLt) F x) (by positivity)

end EinsteinFull
