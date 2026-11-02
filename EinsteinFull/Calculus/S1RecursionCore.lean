import EinsteinFull.Calculus.S1RecursionInstantiate

/-! The core of the dyadic block recursion, for an arbitrary finite family of local
stationary fields: all estimates enter as hypotheses about the block vectors. -/

open MeasureTheory ProbabilityTheory

namespace EinsteinFull.Calculus.S1
open EinsteinFull EinsteinRelation

variable {d : ℕ}

theorem recursion_core {μ : Measure (FieldPair d)} [IsProbabilityMeasure μ]
    {ι : Type*} [Fintype ι] {V₁ V₂ : Vec d → Set (Vec d)}
    {F₁ F₂ : ι → Vec d → FieldPair d → ℝ} {r₀ ρ L w n n₂ Cc B H : ℝ}
    (hfr : HasFiniteRange r₀ μ) (hT : ∀ x, MeasurePreserving (translate x) μ μ)
    (hV₁ : ∀ y z, z ∈ V₁ y → euclideanNorm (z - y) < ρ)
    (hs : r₀ < L - (L - w) - 2 * ρ) (hw : 0 ≤ w)
    (hn₂ : n₂ = (2 : ℝ) ^ (-(d : ℝ) / 2) * n)
    (hc : ((2 : ℝ) ^ (-(d : ℝ) / 2)) ^ 2 * (Fintype.card (Fin d → Fin 2) : ℝ) = 1)
    (lsf1 : ∀ a, LocalStationaryField μ V₁ (F₁ a))
    (lsf2 : ∀ a, LocalStationaryField μ V₂ (F₂ a))
    (hXL2 : L2Vec μ (blk n F₁ (clockBlockCube 0 L) (fun _ => (1 : ℝ))))
    (hXc : vl2 μ (blk n F₁ (clockBlockCube 0 L) (fun _ => (1 : ℝ))) ≤ Cc)
    (hXmL2 : L2Vec μ (blk n F₁ (clockBlockCube 0 (L - w)) (fun _ => (1 : ℝ))))
    (hXmc : vl2 μ (blk n F₁ (clockBlockCube 0 (L - w)) (fun _ => (1 : ℝ))) ≤ Cc)
    (hX₂L2 : L2Vec μ (blk n₂ F₂ (clockBlockCube 0 (2 * L)) (fun _ => (1 : ℝ))))
    (hX₂c : vl2 μ (blk n₂ F₂ (clockBlockCube 0 (2 * L)) (fun _ => (1 : ℝ))) ≤ Cc)
    (hsbL2 : ∀ x, L2Vec μ (blk n F₁ (clockBlockCube x L) (stripFn x L w)))
    (hsbc : ∀ x, vl2 μ (blk n F₁ (clockBlockCube x L) (stripFn x L w)) ≤ B)
    (hΔL2 : ∀ x, L2Vec μ (fun ω a => blk n F₂ (clockBlockCube x L) (fun _ => (1 : ℝ)) ω a -
      blk n F₁ (clockBlockCube x L) (fun _ => (1 : ℝ)) ω a))
    (hΔc : ∀ x, vl2 μ (fun ω a => blk n F₂ (clockBlockCube x L) (fun _ => (1 : ℝ)) ω a -
      blk n F₁ (clockBlockCube x L) (fun _ => (1 : ℝ)) ω a) ≤ H) :
    L2Vec μ (fun ω a => blk n F₁ (clockBlockCube 0 L) (fun _ => (1 : ℝ)) ω a -
        blk n F₁ (clockBlockCube 0 (L - w)) (fun _ => (1 : ℝ)) ω a) ∧
    vl2 μ (fun ω a => blk n F₁ (clockBlockCube 0 L) (fun _ => (1 : ℝ)) ω a -
        blk n F₁ (clockBlockCube 0 (L - w)) (fun _ => (1 : ℝ)) ω a) ≤ B ∧
    iIndepFun (fun j : Fin d → Fin 2 =>
        blk n F₁ (clockBlockCube (childCenter L j) (L - w)) (fun _ => (1 : ℝ))) μ ∧
    (∀ j : Fin d → Fin 2, IdentDistrib
        (blk n F₁ (clockBlockCube (childCenter L j) (L - w)) (fun _ => (1 : ℝ)))
        (blk n F₁ (clockBlockCube 0 (L - w)) (fun _ => (1 : ℝ))) μ μ) ∧
    (∀ (j : Fin d → Fin 2) (a : ι),
        Integrable (fun ω => blk n F₁ (clockBlockCube (childCenter L j) (L - w))
          (fun _ => (1 : ℝ)) ω a) μ ∧
        ∫ ω, blk n F₁ (clockBlockCube (childCenter L j) (L - w)) (fun _ => (1 : ℝ)) ω a ∂μ = 0) ∧
    L2Vec μ (fun ω a => blk n₂ F₂ (clockBlockCube 0 (2 * L)) (fun _ => (1 : ℝ)) ω a -
        (2 : ℝ) ^ (-(d : ℝ) / 2) * ∑ j : Fin d → Fin 2,
          blk n F₁ (clockBlockCube (childCenter L j) (L - w)) (fun _ => (1 : ℝ)) ω a) ∧
    vl2 μ (fun ω a => blk n₂ F₂ (clockBlockCube 0 (2 * L)) (fun _ => (1 : ℝ)) ω a -
        (2 : ℝ) ^ (-(d : ℝ) / 2) * ∑ j : Fin d → Fin 2,
          blk n F₁ (clockBlockCube (childCenter L j) (L - w)) (fun _ => (1 : ℝ)) ω a) ≤
      (2 : ℝ) ^ (-(d : ℝ) / 2) * ((Fintype.card (Fin d → Fin 2) : ℝ) * (H + B)) ∧
    frob (covMat μ (blk n₂ F₂ (clockBlockCube 0 (2 * L)) (fun _ => (1 : ℝ))) -
        covMat μ (blk n F₁ (clockBlockCube 0 L) (fun _ => (1 : ℝ)))) ≤
      ((2 : ℝ) ^ (-(d : ℝ) / 2) * ((Fintype.card (Fin d → Fin 2) : ℝ) * (H + B))) *
          (2 * Cc + (2 : ℝ) ^ (-(d : ℝ) / 2) * ((Fintype.card (Fin d → Fin 2) : ℝ) * (H + B))) +
        B * (2 * Cc) := by
  have hcpos : 0 < (2 : ℝ) ^ (-(d : ℝ) / 2) := Real.rpow_pos_of_pos (by norm_num) _
  -- the strip identity at the origin
  have hdiff_ae : (fun ω a => blk n F₁ (clockBlockCube 0 L) (fun _ => (1 : ℝ)) ω a -
        blk n F₁ (clockBlockCube 0 (L - w)) (fun _ => (1 : ℝ)) ω a) =ᵐ[μ]
      blk n F₁ (clockBlockCube 0 L) (stripFn 0 L w) :=
    (blk_strip_decomp lsf1 hT n L w hw 0).mono fun ω hω => funext hω
  have hdiffL2 : L2Vec μ (fun ω a => blk n F₁ (clockBlockCube 0 L) (fun _ => (1 : ℝ)) ω a -
        blk n F₁ (clockBlockCube 0 (L - w)) (fun _ => (1 : ℝ)) ω a) :=
    (hsbL2 0).congr_ae hdiff_ae.symm
  have hdiffc : vl2 μ (fun ω a => blk n F₁ (clockBlockCube 0 L) (fun _ => (1 : ℝ)) ω a -
        blk n F₁ (clockBlockCube 0 (L - w)) (fun _ => (1 : ℝ)) ω a) ≤ B := by
    rw [vl2_congr_ae hdiff_ae]
    exact hsbc 0
  -- children
  have hid : ∀ j : Fin d → Fin 2, IdentDistrib
      (blk n F₁ (clockBlockCube (childCenter L j) (L - w)) (fun _ => (1 : ℝ)))
      (blk n F₁ (clockBlockCube 0 (L - w)) (fun _ => (1 : ℝ))) μ μ :=
    fun j => blk_identDistrib lsf1 hT n (childCenter L j) (L - w)
  have hind := blk_iIndepFun hfr hV₁ lsf1 hT n hs
  have hintmean : ∀ (j : Fin d → Fin 2) (a : ι),
      Integrable (fun ω => blk n F₁ (clockBlockCube (childCenter L j) (L - w))
        (fun _ => (1 : ℝ)) ω a) μ ∧
      ∫ ω, blk n F₁ (clockBlockCube (childCenter L j) (L - w)) (fun _ => (1 : ℝ)) ω a ∂μ = 0 :=
    fun j a => blk_integrable_mean lsf1 hT n (volume_clockBlockCube_lt_top _ _) a
  have hL2ch : ∀ j : Fin d → Fin 2,
      L2Vec μ (blk n F₁ (clockBlockCube (childCenter L j) (L - w)) (fun _ => (1 : ℝ))) :=
    fun j => blk_L2Vec_of_identDistrib lsf1 hT n (childCenter L j) (L - w) (hid j) hXmL2
  -- the error
  have herr_ae := blk_error_ae lsf1 lsf2 hT hn₂ L w hw
  have hsum := l2_sum_scaled ((2 : ℝ) ^ (-(d : ℝ) / 2))
    (J := Fin d → Fin 2)
    (Δ := fun j ω a => blk n F₂ (clockBlockCube (childCenter L j) L) (fun _ => (1 : ℝ)) ω a -
      blk n F₁ (clockBlockCube (childCenter L j) L) (fun _ => (1 : ℝ)) ω a)
    (S := fun j => blk n F₁ (clockBlockCube (childCenter L j) L)
      (stripFn (childCenter L j) L w))
    (fun j => hΔL2 _) (fun j => hsbL2 _) (fun j => hΔc _) (fun j => hsbc _)
  have herrL2 : L2Vec μ (fun ω a => blk n₂ F₂ (clockBlockCube 0 (2 * L)) (fun _ => (1 : ℝ)) ω a -
        (2 : ℝ) ^ (-(d : ℝ) / 2) * ∑ j : Fin d → Fin 2,
          blk n F₁ (clockBlockCube (childCenter L j) (L - w)) (fun _ => (1 : ℝ)) ω a) :=
    hsum.1.congr_ae herr_ae.symm
  have herrc : vl2 μ (fun ω a => blk n₂ F₂ (clockBlockCube 0 (2 * L)) (fun _ => (1 : ℝ)) ω a -
        (2 : ℝ) ^ (-(d : ℝ) / 2) * ∑ j : Fin d → Fin 2,
          blk n F₁ (clockBlockCube (childCenter L j) (L - w)) (fun _ => (1 : ℝ)) ω a) ≤
      (2 : ℝ) ^ (-(d : ℝ) / 2) * ((Fintype.card (Fin d → Fin 2) : ℝ) * (H + B)) := by
    rw [vl2_congr_ae herr_ae]
    refine hsum.2.trans (le_of_eq ?_)
    rw [abs_of_pos hcpos]
  have hcov := cov_chain (J := Fin d → Fin 2) ((2 : ℝ) ^ (-(d : ℝ) / 2)) hXL2 hXmL2 hX₂L2
    hind hL2ch (fun j a => (hintmean j a).2) hid hc hXc hXmc hX₂c hdiffc herrL2 herrc
  exact ⟨hdiffL2, hdiffc, hind, hid, hintmean, herrL2, herrc, hcov⟩

end EinsteinFull.Calculus.S1
