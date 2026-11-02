import EinsteinFull.Calculus.S1BlockSupport
import EinsteinFull.Calculus.S1CubeSupport
import EinsteinFull.Calculus.S1VectorL2Support

/-! Families of blocks of a stationary local field: translation (identical distribution)
and independence of blocks over separated cubes. -/

open MeasureTheory ProbabilityTheory

namespace EinsteinFull.Calculus.S1
open EinsteinFull EinsteinRelation

variable {d : ℕ}

theorem abs_coord_le_euclideanNorm (z : Vec d) (i : Fin d) : |z i| ≤ euclideanNorm z := by
  unfold euclideanNorm euclideanSq dot
  apply Real.abs_le_sqrt
  calc z i ^ 2 = z i * z i := sq _
    _ ≤ ∑ j, z j * z j :=
        Finset.single_le_sum (f := fun j => z j * z j) (fun j _ => mul_self_nonneg _)
          (Finset.mem_univ i)

theorem integral_comp_measurePreserving' {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ) {f : Ω → ℝ} (hf : AEStronglyMeasurable f μ) :
    ∫ ω, f (T ω) ∂μ = ∫ ω, f ω ∂μ := by
  have hm := integral_map (μ := μ) hT.measurable.aemeasurable (f := f)
    (by rw [hT.map_eq]; exact hf)
  rw [hT.map_eq] at hm
  exact hm.symm

section Field

variable {μ : Measure (FieldPair d)} [IsProbabilityMeasure μ] {V : Vec d → Set (Vec d)}
  {F : Vec d → FieldPair d → ℝ}

omit [IsProbabilityMeasure μ] in
theorem LocalStationaryField.translate_slice_ae (h : LocalStationaryField μ V F)
    (hT : ∀ x, MeasurePreserving (translate x) μ μ) (c y : Vec d) :
    (fun ω => F (c + y) ω) =ᵐ[μ] fun ω => F y (translate c ω) := by
  have h1 := h.stationary (c + y)
  have h2 : (fun ω => F y (translate c ω)) =ᵐ[μ]
      fun ω => F 0 (translate y (translate c ω)) :=
    (hT c).quasiMeasurePreserving.ae_eq_comp (h.stationary y)
  refine h1.trans ?_
  refine Filter.EventuallyEq.trans ?_ h2.symm
  refine Filter.Eventually.of_forall fun ω => ?_
  show F 0 (translate (c + y) ω) = F 0 (translate y (translate c ω))
  rw [translate_add, add_comm c y]

theorem LocalStationaryField.block_translate_ae (h : LocalStationaryField μ V F)
    (hT : ∀ x, MeasurePreserving (translate x) μ μ) (c : Vec d) (L' : ℝ) :
    (fun ω => ∫ y in clockBlockCube c L', F y ω) =ᵐ[μ]
      fun ω => ∫ y in clockBlockCube 0 L', F y (translate c ω) := by
  have e : (fun ω => ∫ y in clockBlockCube c L', F y ω) =
      fun ω => ∫ y in clockBlockCube 0 L', F (c + y) ω := by
    funext ω
    have := setIntegral_clockBlockCube_add (fun y => F y ω) c 0 L'
    rwa [add_zero] at this
  rw [e]
  have hfin := volume_clockBlockCube_lt_top (d := d) 0 L'
  have hK : ∀ y, ∫ ω, ‖F y ω‖ ∂μ ≤ ∫ ω, ‖F 0 ω‖ ∂μ := fun y => (h.integral_norm_eq hT y).le
  have i1 : Integrable (fun p : Vec d × FieldPair d => F (c + p.1) p.2)
      ((volume.restrict (clockBlockCube 0 L')).prod μ) :=
    integrable_prod_of_slice_bound (G := fun y ω => F (c + y) ω) hfin
      (h.meas.comp_quasiMeasurePreserving
        ((measurePreserving_add_left volume c).prod (MeasurePreserving.id μ)).quasiMeasurePreserving)
      (fun y => (h.memLp (c + y)).integrable one_le_two)
      (K := ∫ ω, ‖F 0 ω‖ ∂μ) (fun y => hK (c + y))
  have i2 : Integrable (fun p : Vec d × FieldPair d => F p.1 (translate c p.2))
      ((volume.restrict (clockBlockCube 0 L')).prod μ) :=
    integrable_prod_of_slice_bound (G := fun y ω => F y (translate c ω)) hfin
      (h.meas.comp_quasiMeasurePreserving
        ((MeasurePreserving.id volume).prod (hT c)).quasiMeasurePreserving)
      (fun y => (hT c).integrable_comp_of_integrable ((h.memLp y).integrable one_le_two))
      (K := ∫ ω, ‖F 0 ω‖ ∂μ) (fun y => by
        rw [integral_comp_measurePreserving' (f := fun ω => ‖F y ω‖) (hT c)
          (h.memLp y).aestronglyMeasurable.norm]
        exact hK y)
  exact integral_aeEq_of_slice_aeEq i1 i2
    (Filter.Eventually.of_forall fun y => h.translate_slice_ae hT c y)

end Field

section Family

variable {μ : Measure (FieldPair d)} [IsProbabilityMeasure μ] {V : Vec d → Set (Vec d)}
  {ι : Type*} [Fintype ι] {Fv : ι → Vec d → FieldPair d → ℝ}

theorem aemeasurable_block_vec (h : ∀ a, LocalStationaryField μ V (Fv a))
    (hT : ∀ x, MeasurePreserving (translate x) μ μ) (n : ℝ) (C : Set (Vec d))
    (hC : volume C < ⊤) :
    AEMeasurable (fun ω a => n * ∫ y in C, Fv a y ω) μ :=
  aemeasurable_pi_iff.2 fun a =>
    (((h a).integrable_block hT hC).aestronglyMeasurable.const_mul n).aemeasurable

theorem blocks_identDistrib (h : ∀ a, LocalStationaryField μ V (Fv a))
    (hT : ∀ x, MeasurePreserving (translate x) μ μ) (n : ℝ) (c : Vec d) (L' : ℝ) :
    IdentDistrib (fun ω a => n * ∫ y in clockBlockCube c L', Fv a y ω)
      (fun ω a => n * ∫ y in clockBlockCube 0 L', Fv a y ω) μ μ := by
  have hf := aemeasurable_block_vec h hT n (clockBlockCube c L')
    (volume_clockBlockCube_lt_top c L')
  have hg := aemeasurable_block_vec h hT n (clockBlockCube 0 L')
    (volume_clockBlockCube_lt_top 0 L')
  have hfg : (fun ω a => n * ∫ y in clockBlockCube c L', Fv a y ω) =ᵐ[μ]
      (fun ω a => n * ∫ y in clockBlockCube 0 L', Fv a y ω) ∘ translate c := by
    have : ∀ᵐ ω ∂μ, ∀ a, ∫ y in clockBlockCube c L', Fv a y ω =
        ∫ y in clockBlockCube 0 L', Fv a y (translate c ω) :=
      ae_all_iff.2 fun a => (h a).block_translate_ae hT c L'
    filter_upwards [this] with ω hω
    funext a
    simp only [Function.comp_apply, hω a]
  refine ⟨hf, hg, ?_⟩
  have hmm : (μ.map (translate c)).map
      (fun ω a => n * ∫ y in clockBlockCube 0 L', Fv a y ω) =
      μ.map ((fun ω a => n * ∫ y in clockBlockCube 0 L', Fv a y ω) ∘ translate c) :=
    AEMeasurable.map_map_of_aemeasurable (by rw [(hT c).map_eq]; exact hg)
      (hT c).measurable.aemeasurable
  rw [Measure.map_congr hfg, ← hmm, (hT c).map_eq]

/-- Blocks over cubes of side `L'` whose centres are `L`-separated in some coordinate are
independent once the localization radius `ρ` satisfies `r₀ < L - L' - 2ρ`. -/
theorem blocks_iIndepFun {r₀ ρ L L' : ℝ} (hfr : HasFiniteRange r₀ μ)
    (hV : ∀ y z, z ∈ V y → euclideanNorm (z - y) < ρ)
    (h : ∀ a, LocalStationaryField μ V (Fv a))
    (hT : ∀ x, MeasurePreserving (translate x) μ μ) (n : ℝ)
    (hs : r₀ < L - L' - 2 * ρ) :
    iIndepFun (fun (j : Fin d → Fin 2) ω a =>
      n * ∫ y in clockBlockCube (childCenter L j) L', Fv a y ω) μ := by
  classical
  set U : (Fin d → Fin 2) → Set (Vec d) :=
    fun j => clockBlockCube (childCenter L j) (L' + 2 * ρ) with hUdef
  have hU : ∀ j, MeasurableSet (U j) := fun j => measurableSet_clockBlockCube _ _
  have hsep : ∀ j k, j ≠ k → ∀ x ∈ U j, ∀ y ∈ U k, L - L' - 2 * ρ ≤ euclideanNorm (x - y) := by
    intro j k hjk x hx y hy
    rw [hUdef] at hx hy
    simp only [mem_clockBlockCube_iff] at hx hy
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hjk
    have hxi := hx i
    have hyi := hy i
    simp only [childCenter] at hxi hyi
    have hcoord : |(x - y) i| ≤ euclideanNorm (x - y) := abs_coord_le_euclideanNorm _ i
    have hcases : (j i = 0 ∧ k i ≠ 0) ∨ (j i ≠ 0 ∧ k i = 0) := by
      revert hi
      generalize j i = a
      generalize k i = b
      fin_cases a <;> fin_cases b <;> simp
    refine le_trans ?_ hcoord
    rcases hcases with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · simp only [ha, hb, ite_true, ite_false] at hxi hyi
      rw [Pi.sub_apply, abs_sub_comm]
      exact le_trans (by linarith [hxi.2, hyi.1]) (le_abs_self _)
    · simp only [ha, hb, ite_true, ite_false] at hxi hyi
      rw [Pi.sub_apply]
      exact le_trans (by linarith [hxi.1, hyi.2]) (le_abs_self _)
  have hloc : ∀ (a : ι) (j : Fin d → Fin 2), ∃ H : FieldPair d → ℝ,
      StronglyMeasurable[localSigma (U j)] H ∧
        (fun ω => ∫ y in clockBlockCube (childCenter L j) L', Fv a y ω) =ᵐ[μ] H := by
    intro a j
    refine (h a).block_local hT (measurableSet_clockBlockCube _ _)
      (volume_clockBlockCube_lt_top _ _) (U := U j) ?_
    intro y hy z hz
    have hz' := hV y z hz
    rw [mem_clockBlockCube_iff] at hy
    rw [hUdef]
    simp only [mem_clockBlockCube_iff]
    intro i
    have h1 : |(z - y) i| ≤ euclideanNorm (z - y) := abs_coord_le_euclideanNorm _ i
    have h2 := abs_lt.1 (lt_of_le_of_lt h1 hz')
    have h3 := hy i
    simp only [Pi.sub_apply] at h2
    exact ⟨by linarith [h2.1, h3.1], by linarith [h2.2, h3.2]⟩
  choose H hHm hH using hloc
  refine iIndepFun_of_local hfr U hU (s := L - L' - 2 * ρ) hs hsep
    (g := fun j ω a => n * H a j ω) ?_ ?_
  · intro j
    letI : MeasurableSpace (FieldPair d) := localSigma (U j)
    exact measurable_pi_iff.2 fun a =>
      (measurable_const.mul measurable_id).comp (hHm a j).measurable
  · intro j
    have : ∀ᵐ ω ∂μ, ∀ a, ∫ y in clockBlockCube (childCenter L j) L', Fv a y ω = H a j ω :=
      ae_all_iff.2 fun a => hH a j
    filter_upwards [this] with ω hω
    funext a
    simp only [hω a]

end Family

end EinsteinFull.Calculus.S1
