import EinsteinRelation.Calculus.CoordinateTranslationPath

noncomputable section
namespace EinsteinRelation

/-- Telescoping sum: ∑_{k=0}^{d-1} (a(k+1) - a(k)) = a(d) - a(0) -/
lemma telescoping_sum (a : ℕ → ℝ) (d : ℕ) :
    (∑ k ∈ Finset.range d, (a (k + 1) - a k)) = a d - a 0 := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Finset.sum_range_succ, ih]
      ring

/-- The endpoint differences of the coordinate path telescope exactly
(`paper/main.tex:1021–1029`). -/
theorem sum_coordinatePath_endpoints {d : ℕ} (z : Vec d) (f : FieldPair d → ℝ)
    (ω : FieldPair d) :
    (∑ i : Fin d, (f (translate (coordinateSegment z i (z i)) ω) -
      f (translate (coordinateSegment z i 0) ω))) = f (translate z ω) - f ω := by
  -- define a_k = f(translate (coordinatePrefix z k) ω)
  let a : ℕ → ℝ := fun k => f (translate (coordinatePrefix z k) ω)
  have ha0 : a 0 = f ω := by
    dsimp [a]
    have h0 : coordinatePrefix z 0 = 0 := by
      ext j; simp [coordinatePrefix]
    rw [h0, translate_zero]
  have had : a d = f (translate z ω) := by
    dsimp [a]
    have hd : coordinatePrefix z d = z := by
      ext j; simp [coordinatePrefix]
    rw [hd]
  have hpos : ∀ (i : Fin d), f (translate (coordinateSegment z i (z i)) ω) = a (i.val + 1) := by
    intro i
    dsimp [a, coordinateSegment]
    have h_eq : coordinatePrefix z i.val + (z i) • unitVector i = coordinatePrefix z (i.val + 1) := by
      ext j
      dsimp [coordinatePrefix, unitVector]
      by_cases h_lt : j.val < i.val
      · have h_lt' : j.val < i.val + 1 := by
          simpa [Nat.succ_eq_add_one] using Nat.lt_succ_of_le (Nat.le_of_lt h_lt)
        have h_ne : j ≠ i := by
          intro h_eq
          have h_val_eq : j.val = i.val := congrArg Fin.val h_eq
          linarith
        simp [h_lt, h_lt', h_ne]
      · by_cases h_eq_val : j.val = i.val
        · have h_lt' : j.val < i.val + 1 := by
            rw [h_eq_val]
            simpa [Nat.succ_eq_add_one] using Nat.lt_succ_self (i.val)
          have h_ji : j = i := Fin.ext h_eq_val
          subst h_ji
          simp [Pi.single]
        · have h_not_lt : ¬ (j.val < i.val + 1) := by
            intro h
            have hle : i.val ≤ j.val := Nat.ge_of_not_lt h_lt
            rcases Nat.lt_or_eq_of_le hle with (hlt' | heq')
            · have hle' : i.val + 1 ≤ j.val := Nat.succ_le_of_lt hlt'
              linarith
            · exact h_eq_val heq'.symm
          have h_ne : j ≠ i := by
            intro h
            apply h_eq_val
            simpa [h] using rfl
          simp [h_lt, h_not_lt, h_ne]
    rw [h_eq]
  have hneg : ∀ (i : Fin d), f (translate (coordinateSegment z i 0) ω) = a (i.val) := by
    intro i
    dsimp [a, coordinateSegment]
    simp
  rw [Finset.sum_congr rfl (fun i _ => by rw [hpos i, hneg i])]
  -- Now we need: ∑ i : Fin d, (a (i.val + 1) - a (i.val)) = a d - a 0
  rw [Fin.sum_univ_eq_sum_range (fun k => a (k + 1) - a k) d]
  -- Now: ∑ k ∈ range d, (a (k + 1) - a k) = a d - a 0
  rw [telescoping_sum a d]
  -- Now: a d - a 0 = f (translate z ω) - f ω
  rw [ha0, had]

end EinsteinRelation
