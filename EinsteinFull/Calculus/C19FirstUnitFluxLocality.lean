import EinsteinFull.Calculus.C19FirstUnitTransposeProjection
import EinsteinFull.Calculus.C10FirstUnitFluxSize
import EinsteinFull.Calculus.C7DyadicFluxDecomposition
import EinsteinFull.Blueprint.G3.Proofs.C9DyadicIncrements

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation

private theorem local_radius_mono {d : ℕ} {Λ r₀ r R : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (hr : r ≤ R)
    {f : Lp ℂ 2 (reducedLaw Q)} (hf : IsComplexLocalObservation Q r f) :
    IsComplexLocalObservation Q R f := by
  obtain ⟨g, hg, he⟩ := hf
  exact ⟨g, hg.mono (Probability.localSigma_mono (fun _ hx => hx.trans_le hr)) le_rfl, he⟩

/-- Assemble independently localized integrated gradients and the already
force-weighted transpose primitive, preserving the original supplied flux. -/
private theorem weighted_flux_approximation
    {d : ℕ} (hd : 2 ≤ d) {Λ r₀ ρ : ℝ} (Q : EnvironmentLaw d Λ r₀)
    (hρ : 0 < ρ) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (ha : IsReducedCoefficientObservation Q a)
    (G F : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (hF : IsFiniteTimeFlux hd Q ζ P Pdag β a μ G F) (ν : FluxIndex d)
    (g : Fin d → Lp ℂ 2 (reducedLaw Q)) (w : Lp ℂ 2 (reducedLaw Q))
    (hg : ∀ k, IsComplexLocalObservation Q ρ (g k))
    (hw : IsComplexLocalObservation Q ρ w) :
    ∃ V : Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ j, IsComplexLocalObservation Q ρ (V j)) ∧
      Real.sqrt (∑ j, ‖F 1 ν j - F 0 ν j - V j‖ ^ 2) ≤
        (d : ℝ) * (Real.exp (2 * Λ) * Λ) *
          ((∑ k, ‖(∫ r in Icc (0 : ℝ) 1, G r.toNNReal ν k) - g k‖) +
            ‖(-2 * ζ) • (∫ r in Icc (0 : ℝ) 1,
              transposeEndpoint Q ⟨0, by omega⟩ Pdag β r.toNNReal) - w‖) := by
  classical
  let H := fun k => ∫ r in Icc (0 : ℝ) 1, G r.toNNReal ν k
  let U := (-2 * ζ) • (∫ r in Icc (0 : ℝ) 1,
    transposeEndpoint Q ⟨0, by omega⟩ Pdag β r.toNNReal)
  let K := Real.exp (2 * Λ) * Λ
  let E := (∑ k, ‖H k - g k‖) + ‖U - w‖
  let V := fun j => (∑ k, complexCoefficientMul Q j k (g k)) +
    ν.elim (fun _ => 0) (fun _ => complexCoefficientMul Q j ⟨0, by omega⟩ w)
  have hK : 0 ≤ K := mul_nonneg (Real.exp_pos _).le
    (zero_le_one.trans Q.ellipticity_parameter)
  have hmul (j k : Fin d) (v : Lp ℂ 2 (reducedLaw Q)) :
      ‖complexCoefficientMul Q j k v‖ ≤ K * ‖v‖ :=
    ((complexCoefficientMul Q j k).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (norm_complexCoefficientMul_le Q j k) (norm_nonneg _))
  have hrow (j : Fin d) :
      ‖∑ k, complexCoefficientMul Q j k (H k - g k)‖ ≤ K * ∑ k, ‖H k - g k‖ := by
    calc
      _ ≤ ∑ k, ‖complexCoefficientMul Q j k (H k - g k)‖ := norm_sum_le _ _
      _ ≤ ∑ k, K * ‖H k - g k‖ := Finset.sum_le_sum (fun k _ => hmul j k _)
      _ = _ := (Finset.mul_sum _ _ _).symm
  have htrans (j : Fin d) :
      ‖ν.elim (fun _ => 0) (fun _ => complexCoefficientMul Q j ⟨0, by omega⟩ (U - w))‖ ≤
        K * ‖U - w‖ := by
    cases ν with
    | inl i => simp only [Sum.elim_inl, norm_zero]; positivity
    | inr b => exact hmul j _ _
  obtain ⟨Y, B, _, _, hsplit, hY, hB⟩ :=
    dyadic_flux_decomposition hd Q ζ P Pdag β a μ ha G F hF 0 1 (by norm_num) ν
  have he (j : Fin d) : F 1 ν j - F 0 ν j - V j =
      (∑ k, complexCoefficientMul Q j k (H k - g k)) +
        ν.elim (fun _ => 0) (fun _ => complexCoefficientMul Q j ⟨0, by omega⟩ (U - w)) := by
    rw [hsplit j, hY j, hB j]
    dsimp only [V, H, U]
    simp only [map_sub, map_smul, Finset.sum_sub_distrib, NNReal.coe_zero, NNReal.coe_one]
    cases ν <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> abel
  have hcoord (j : Fin d) : ‖F 1 ν j - F 0 ν j - V j‖ ≤ K * E := by
    rw [he]
    exact ((norm_add_le _ _).trans (add_le_add (hrow j) (htrans j))).trans_eq
      (by dsimp only [E]; ring)
  refine ⟨V, ?_, ?_⟩
  · intro j
    have hsum : C9ShortTimeLocality.localProjection Q ρ
        (∑ k, complexCoefficientMul Q j k (g k)) = ∑ k, complexCoefficientMul Q j k (g k) := by
      rw [map_sum]
      exact Finset.sum_congr rfl (fun k _ =>
        C9ShortTimeLocality.localProjection_of_isLocal Q ρ
          (C9DyadicIncrements.complexCoefficientMul_isLocal Q hρ j k (hg k)))
    have ht : C9ShortTimeLocality.localProjection Q ρ
        (ν.elim (fun _ => 0) (fun _ => complexCoefficientMul Q j ⟨0, by omega⟩ w)) =
        ν.elim (fun _ => 0) (fun _ => complexCoefficientMul Q j ⟨0, by omega⟩ w) := by
      cases ν with
      | inl i => exact map_zero _
      | inr b =>
          exact C9ShortTimeLocality.localProjection_of_isLocal Q ρ
            (C9DyadicIncrements.complexCoefficientMul_isLocal Q hρ j _ hw)
    have hv := C9ShortTimeLocality.localProjection_isLocal Q ρ (V j)
    dsimp only [V] at hv ⊢
    rwa [map_add, hsum, ht] at hv
  · change Real.sqrt (∑ j, ‖F 1 ν j - F 0 ν j - V j‖ ^ 2) ≤ (d : ℝ) * K * E
    calc
      _ ≤ ∑ j, ‖F 1 ν j - F 0 ν j - V j‖ := by
        apply Real.sqrt_le_iff.mpr
        exact ⟨Finset.sum_nonneg (fun _ _ => norm_nonneg _),
          Finset.sum_sq_le_sq_sum_of_nonneg (fun _ _ => norm_nonneg _)⟩
      _ ≤ ∑ _j : Fin d, K * E := Finset.sum_le_sum (fun j _ => hcoord j)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- Gaussian locality of the original first-unit flux increment, uniformly in the supplied law. -/
theorem c19_first_unit_flux_locality (hlocal : node_l_u3A_forced_u2D_localStmt) : ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d), ∃ C c : ℝ, 1 ≤ C ∧ 0 < c ∧ ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)), IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ → ∀ (ζ : ℂ) (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)), IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P → IsComplexTransposeSemigroup Q P Pdag → ∀ (G F : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q)), IsFiniteTimeFlux hd Q ζ P Pdag β a μ G F → ‖ζ‖ ≤ 2 → ∀ ν : FluxIndex d, Real.sqrt (∑ j : Fin d, ‖F 1 ν j - F 0 ν j‖ ^ 2) ≤ C ∧ ∀ n : ℕ, 1 ≤ n → ∃ V : Fin d → Lp ℂ 2 (reducedLaw Q), (∀ j, IsComplexLocalObservation Q (C * (n : ℝ)) (V j)) ∧ Real.sqrt (∑ j : Fin d, ‖F 1 ν j - F 0 ν j - V j‖ ^ 2) ≤ C * Real.exp (-c * (n : ℝ) ^ 2) := by
  classical
  intro d hd D
  obtain ⟨Cg, cg, hCg, hcg, hg⟩ :=
    c19_first_unit_integrated_gradient_projection_error hlocal d hd D
  obtain ⟨Ct, ct, hCt, hct, ht⟩ :=
    c19_first_unit_transpose_projection_error d hd D
  obtain ⟨Cs, hCs, hs⟩ := first_unit_flux_size d hd D
  let K := Real.exp (2 * D.ellipticity) * D.ellipticity
  let A := (d : ℝ) * K * ((d : ℝ) * Cg + Ct)
  let C := max (max 1 Cs) (max (max Cg Ct) A)
  have hC : 1 ≤ C := (le_max_left 1 Cs).trans (le_max_left _ _)
  have hCsC : Cs ≤ C := (le_max_right 1 Cs).trans (le_max_left _ _)
  have hCgC : Cg ≤ C := (le_max_left Cg Ct).trans
    ((le_max_left _ _).trans (le_max_right _ _))
  have hCtC : Ct ≤ C := (le_max_right Cg Ct).trans
    ((le_max_left _ _).trans (le_max_right _ _))
  have hAC : A ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have hK : 0 ≤ K := mul_nonneg (Real.exp_nonneg _)
    (zero_le_one.trans D.one_le_ellipticity)
  refine ⟨C, min cg ct, hC, lt_min hcg hct, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd G F hF hζ ν
  refine ⟨(hs Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd G F hF hζ ν).trans hCsC, ?_⟩
  intro n hn
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hnp : 0 < (n : ℝ) := by exact_mod_cast (zero_lt_one.trans_le hn)
  let H := fun k => ∫ r in Icc (0 : ℝ) 1, G r.toNNReal ν k
  let U := (-2 * ζ) • (∫ r in Icc (0 : ℝ) 1,
    transposeEndpoint Q ⟨0, by omega⟩ Pdag β r.toNNReal)
  let g := fun k => C9ShortTimeLocality.localProjection Q (Cg * (n : ℝ)) (H k)
  let w := C9ShortTimeLocality.localProjection Q (Ct * (n : ℝ)) U
  let e := Real.exp (-(min cg ct) * (n : ℝ) ^ 2)
  have hexpg : Real.exp (-cg * (n : ℝ) ^ 2) ≤ e := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (neg_le_neg (min_le_left _ _)) (sq_nonneg _)
  have hexpt : Real.exp (-ct * (n : ℝ) ^ 2) ≤ e := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (neg_le_neg (min_le_right _ _)) (sq_nonneg _)
  have hge : Real.sqrt (∑ k, ‖H k - g k‖ ^ 2) ≤ Cg * e :=
    (hg Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd G F hF hζ ν n hn).trans
      (mul_le_mul_of_nonneg_left hexpg (zero_le_one.trans hCg))
  have hwe : ‖U - w‖ ≤ Ct * e :=
    (ht Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd hζ n hn).trans
      (mul_le_mul_of_nonneg_left hexpt (zero_le_one.trans hCt))
  have hsum : (∑ k, ‖H k - g k‖) ≤ (d : ℝ) * (Cg * e) := by
    calc
      _ ≤ ∑ _k : Fin d, Cg * e := by
        apply Finset.sum_le_sum
        intro k _
        apply le_trans _ hge
        calc
          _ = Real.sqrt (‖H k - g k‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
          _ ≤ Real.sqrt (∑ l : Fin d, ‖H l - g l‖ ^ 2) := Real.sqrt_le_sqrt
            (Finset.single_le_sum (fun l _ => sq_nonneg ‖H l - g l‖) (Finset.mem_univ k))
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  obtain ⟨V, hV, he⟩ := weighted_flux_approximation hd Q
    (mul_pos (zero_lt_one.trans_le hC) hnp) ζ P Pdag β a μ ha G F hF ν g w
    (fun k => local_radius_mono Q (mul_le_mul_of_nonneg_right hCgC hn0)
      (C9ShortTimeLocality.localProjection_isLocal Q (Cg * (n : ℝ)) (H k)))
    (local_radius_mono Q (mul_le_mul_of_nonneg_right hCtC hn0)
      (C9ShortTimeLocality.localProjection_isLocal Q (Ct * (n : ℝ)) U))
  refine ⟨V, hV, he.trans ?_⟩
  change (d : ℝ) * K * ((∑ k, ‖H k - g k‖) + ‖U - w‖) ≤ C * e
  calc
    _ ≤ (d : ℝ) * K * ((d : ℝ) * (Cg * e) + Ct * e) :=
      mul_le_mul_of_nonneg_left (add_le_add hsum hwe) (mul_nonneg (Nat.cast_nonneg _) hK)
    _ = A * e := by dsimp only [A]; ring
    _ ≤ C * e := mul_le_mul_of_nonneg_right hAC (Real.exp_nonneg _)

end EinsteinFull.Blueprint
