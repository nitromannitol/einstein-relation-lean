import EinsteinFull.Calculus.S1BlockFamilySupport

/-! Algebra of blocks used in the dyadic recursion: indicator restrictions of blocks,
congruence of `L2Vec`, and the second-moment matrix of a sum of independent, centered,
identically distributed blocks. -/

open MeasureTheory ProbabilityTheory

namespace EinsteinFull.Calculus.S1
open EinsteinFull EinsteinRelation

variable {d : ℕ}

theorem indicator_one_mul_eq (T : Set (Vec d)) (G : Vec d → ℝ) (y : Vec d) :
    T.indicator (fun _ => (1 : ℝ)) y * G y = T.indicator G y := by
  by_cases h : y ∈ T <;> simp [Set.indicator, h]

theorem indicator_compl_one_mul_eq (T : Set (Vec d)) (G : Vec d → ℝ) (y : Vec d) :
    Tᶜ.indicator (fun _ => (1 : ℝ)) y * G y = G y - T.indicator G y := by
  by_cases h : y ∈ T <;> simp [Set.indicator, h]

theorem setIntegral_indicator_one_mul {S T : Set (Vec d)} (hT : MeasurableSet T)
    (hTS : T ⊆ S) (G : Vec d → ℝ) :
    ∫ y in S, T.indicator (fun _ => (1 : ℝ)) y * G y = ∫ y in T, (fun _ => (1 : ℝ)) y * G y := by
  simp only [indicator_one_mul_eq, one_mul]
  rw [setIntegral_indicator hT, Set.inter_eq_right.2 hTS]

theorem setIntegral_sub_indicator {S T : Set (Vec d)} (hT : MeasurableSet T)
    (hTS : T ⊆ S) {G : Vec d → ℝ} (hG : IntegrableOn G S) :
    (∫ y in S, (fun _ => (1 : ℝ)) y * G y) - ∫ y in T, (fun _ => (1 : ℝ)) y * G y =
      ∫ y in S, Tᶜ.indicator (fun _ => (1 : ℝ)) y * G y := by
  simp only [indicator_compl_one_mul_eq, one_mul]
  rw [integral_sub hG (hG.indicator hT), setIntegral_indicator hT, Set.inter_eq_right.2 hTS]

section Congr

variable {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Fintype ι] {μ : Measure Ω}

theorem L2Vec.congr_ae {u v : Ω → ι → ℝ} (hu : L2Vec μ u) (h : u =ᵐ[μ] v) : L2Vec μ v := by
  refine ⟨fun a => (hu.coord_meas a).congr (h.mono fun ω hω => by simp only [hω]), ?_⟩
  exact hu.size_memLp.ae_eq (h.mono fun ω hω => by simp only [hω])

theorem vl2_congr_ae {u v : Ω → ι → ℝ} (h : u =ᵐ[μ] v) : vl2 μ u = vl2 μ v := by
  unfold vl2
  congr 1
  exact integral_congr_ae (h.mono fun ω hω => by simp only [hω])

end Congr

section Cov

variable {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Fintype ι] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
/-- The second-moment matrix of `c ∑ⱼ chⱼ` for independent, centered, identically
distributed square-integrable vectors is `c² · card J` times that of one of them. -/
theorem covMat_sum_indep {J : Type*} [Fintype J] [DecidableEq J] {ch : J → Ω → ι → ℝ}
    {Xm : Ω → ι → ℝ} (c : ℝ) (hind : iIndepFun ch μ) (hL2 : ∀ j, L2Vec μ (ch j))
    (hmean : ∀ j a, ∫ ω, ch j ω a ∂μ = 0) (hid : ∀ j, IdentDistrib (ch j) Xm μ μ) :
    covMat μ (fun ω a => c * ∑ j, ch j ω a) = (c ^ 2 * (Fintype.card J : ℝ)) • covMat μ Xm := by
  ext a b
  have hprod : ∀ j k, Integrable (fun ω => ch j ω a * ch k ω b) μ := fun j k =>
    ((hL2 j).coord_memLp a).integrable_mul ((hL2 k).coord_memLp b)
  have hinner : ∀ j k, ∫ ω, ch j ω a * ch k ω b ∂μ =
      if j = k then covMat μ Xm a b else 0 := by
    intro j k
    by_cases hjk : j = k
    · subst hjk
      rw [if_pos rfl]
      have h := (hid j).comp (u := fun v : ι → ℝ => v a * v b)
        ((measurable_pi_apply a).mul (measurable_pi_apply b))
      exact h.integral_eq
    · rw [if_neg hjk]
      have hi : IndepFun (fun ω => ch j ω a) (fun ω => ch k ω b) μ :=
        (hind.indepFun hjk).comp (measurable_pi_apply a) (measurable_pi_apply b)
      rw [hi.integral_fun_mul_eq_mul_integral ((hL2 j).coord_meas a) ((hL2 k).coord_meas b),
        hmean j a, zero_mul]
  show ∫ ω, (c * ∑ j, ch j ω a) * (c * ∑ k, ch k ω b) ∂μ =
    c ^ 2 * (Fintype.card J : ℝ) * ∫ ω, Xm ω a * Xm ω b ∂μ
  have e1 : ∀ ω, (c * ∑ j, ch j ω a) * (c * ∑ k, ch k ω b) =
      c ^ 2 * ∑ j, ∑ k, ch j ω a * ch k ω b := by
    intro ω
    rw [mul_mul_mul_comm, Finset.sum_mul_sum]
    ring
  simp_rw [e1]
  rw [integral_const_mul, integral_finset_sum _ (fun j _ =>
    integrable_finset_sum _ fun k _ => hprod j k)]
  have e2 : ∀ j, ∫ ω, ∑ k, ch j ω a * ch k ω b ∂μ = ∫ ω, Xm ω a * Xm ω b ∂μ := by
    intro j
    rw [integral_finset_sum _ (fun k _ => hprod j k)]
    simp only [hinner j, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rfl
  simp only [e2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

end Cov

end EinsteinFull.Calculus.S1
