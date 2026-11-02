import EinsteinFull.Calculus.C17TubeParabolicScaling
import EinsteinFull.Calculus.C9TubeNativeCutoffSurvival
import EinsteinFull.Calculus.C13TubeGeneralChainAssembly

open EinsteinRelation MeasureTheory EinsteinFull.External.Source.GMP
open scoped Topology

namespace EinsteinFull.Calculus

/-- The literal unit-cylinder pointwise comparison, with its constant fixed
before the coefficients and the solution. -/
def BUnitPointwiseHarnack (d : ℕ) (κ : ℝ) : Prop :=
  ∃ H : ℝ, 0 < H ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α → ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G →
    ContinuousOn u (Set.Ioo (-11/16 : ℝ) (-9/16) ×ˢ sourceBall 0 (1/4)) →
    ContinuousOn u (Set.Ioo (1/2 : ℝ) (3/4) ×ˢ sourceBall 0 (1/2)) →
    (∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1), 0 ≤ u z) →
    ∀ x ∈ Set.Ioo (-11/16 : ℝ) (-9/16) ×ˢ sourceBall 0 (1/4),
    ∀ y ∈ Set.Ioo (1/2 : ℝ) (3/4) ×ˢ sourceBall 0 (1/2),
      0 ≤ u y → u x ≤ H * u y

/-- The unit comparison on actual weighted caloric fields is invariant under
centered parabolic affine changes of variables. -/
theorem b_pointwise_harnack_affine_scaling (d : ℕ) (κ : ℝ)
    (hunit : BUnitPointwiseHarnack d κ) :
    ∃ H : ℝ, 0 < H ∧ ∀ (t₀ : ℝ) (x₀ : Vec d) (r : ℝ), 0 < r →
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
    ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α (Set.Ioo (t₀-r^2) (t₀+r^2)) (sourceBall x₀ r) u G →
    ContinuousOn u (Set.Ioo (t₀-r^2) (t₀+r^2) ×ˢ sourceBall x₀ r) →
    (∀ z ∈ Set.Ioo (t₀-r^2) (t₀+r^2) ×ˢ sourceBall x₀ r, 0 ≤ u z) →
    ∀ p ∈ Set.Ioo (-11/16 : ℝ) (-9/16) ×ˢ sourceBall 0 (1/4),
    ∀ q ∈ Set.Ioo (1/2 : ℝ) (3/4) ×ˢ sourceBall 0 (1/2),
    u (t₀+r^2*p.1, x₀+r • p.2) ≤ H * u (t₀+r^2*q.1, x₀+r • q.2) := by
  obtain ⟨H, hH, hunit⟩ := hunit
  refine ⟨H, hH, ?_⟩
  intro t₀ x₀ r hr ρ α hell u G hcal hcont hnonneg p hp q hq
  let F : ℝ × Vec d → ℝ × Vec d := fun z => (t₀+r^2*z.1, x₀+r • z.2)
  have he : IsUniformlyElliptic κ (fun x => ρ (x₀+r • x))
      (fun x => α (x₀+r • x)) :=
    ⟨hell.1.comp (c17_spatial_affine_embedding x₀ hr).measurable,
      hell.2.1.comp (c17_spatial_affine_embedding x₀ hr).measurable, fun x => hell.2.2 _⟩
  have hc : IsWeightedCaloric (fun x => ρ (x₀+r • x)) (fun x => α (x₀+r • x))
      (Set.Ioo (-1) 1) (sourceBall 0 1) (u ∘ F) (fun z => r • G (F z)) :=
    c17_weighted_caloric_parabolic_rescale t₀ x₀ hr ρ α u G hcal
  have hmap : Set.MapsTo F (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1)
      (Set.Ioo (t₀-r^2) (t₀+r^2) ×ˢ sourceBall x₀ r) := by
    intro z hz
    constructor
    · have hr2 : 0 < r^2 := sq_pos_of_pos hr
      constructor <;> nlinarith [hz.1.1, hz.1.2]
    · exact (c17_mem_sourceBall_affine_iff x₀ z.2 hr).2 hz.2
  have hF : Continuous F := by
    dsimp [F]
    fun_prop
  have hcfull : ContinuousOn (u ∘ F) (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1) :=
    hcont.comp hF.continuousOn hmap
  have hearly : Set.Ioo (-11/16 : ℝ) (-9/16) ×ˢ sourceBall (0 : Vec d) (1/4) ⊆
      Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1 := by
    intro z hz
    constructor
    · constructor <;> linarith [hz.1.1, hz.1.2]
    · change euclideanNorm (z.2 - 0) < 1
      have h := hz.2
      change euclideanNorm (z.2 - 0) < (1/4 : ℝ) at h
      linarith
  have hlate : Set.Ioo (1/2 : ℝ) (3/4) ×ˢ sourceBall (0 : Vec d) (1/2) ⊆
      Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall 0 1 := by
    intro z hz
    constructor
    · constructor <;> linarith [hz.1.1, hz.1.2]
    · change euclideanNorm (z.2 - 0) < 1
      have h := hz.2
      change euclideanNorm (z.2 - 0) < (1/2 : ℝ) at h
      linarith
  have hpos : ∀ᵐ z ∂volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ sourceBall (0 : Vec d) 1),
      0 ≤ (u ∘ F) z := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod
      (c17_isOpen_sourceBall (0 : Vec d) 1).measurableSet)] with z hz
    exact hnonneg (F z) (hmap hz)
  exact hunit _ _ he _ _ hc (hcfull.mono hearly) (hcfull.mono hlate) hpos
    p hp q hq (hnonneg (F q) (hmap (hlate hq)))

/-- One-step form of the scaled comparison used in the finite Harnack chain. -/
theorem b_pointwise_harnack_chain_step_of_unit (d : ℕ) (κ : ℝ)
    (hunit : BUnitPointwiseHarnack d κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ), 0 < R → ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α → ∀ (T : ℝ), 0 < T →
    ∀ (v : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α (Set.Ioo 0 (2*T)) (sourceBall 0 R) v G →
    ContinuousOn v (Set.Ioo 0 (2*T) ×ˢ sourceBall 0 R) →
    (∀ p ∈ Set.Ioo 0 (2*T) ×ˢ sourceBall 0 R, 0 ≤ v p) →
    ∀ (s δ : ℝ), 0 < δ → 0 < s - δ → s + 2*δ < 2*T →
    ∀ x y : Vec d, sourceBall x (2*Real.sqrt δ) ⊆ sourceBall 0 R →
    euclideanNorm (y-x)^2 ≤ δ/16 → v (s,x) ≤ C * v (s+δ,y) := by
  obtain ⟨C, hC, hscaled⟩ := b_pointwise_harnack_affine_scaling d κ hunit
  refine ⟨C, hC, ?_⟩
  intro R hR ρ α hell T hT v G hcal hcont hnonneg s δ hδ hs ht x y hball hdist
  let r : ℝ := Real.sqrt (4*δ/5)
  let t₀ : ℝ := s + δ/2
  have hr : 0 < r := Real.sqrt_pos.2 (by positivity)
  have hr2 : r^2 = 4*δ/5 := Real.sq_sqrt (by positivity)
  have hsqrt : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg δ
  have hsqrt2 : Real.sqrt δ ^ 2 = δ := Real.sq_sqrt hδ.le
  have hrbound : r ≤ 2*Real.sqrt δ := by nlinarith [sq_nonneg (r + 2*Real.sqrt δ)]
  have hspace : sourceBall x r ⊆ sourceBall 0 R := by
    intro z hz
    apply hball
    change euclideanNorm (z-x) < 2*Real.sqrt δ
    change euclideanNorm (z-x) < r at hz
    linarith
  have htime : Set.Ioo (t₀-r^2) (t₀+r^2) ⊆ Set.Ioo 0 (2*T) := by
    intro t h
    dsimp [t₀] at h
    rw [hr2] at h
    constructor <;> linarith [h.1, h.2]
  have hsub : Set.Ioo (t₀-r^2) (t₀+r^2) ×ˢ sourceBall x r ⊆
      Set.Ioo 0 (2*T) ×ˢ sourceBall 0 R := Set.prod_mono htime hspace
  have hcal' := c9_weighted_caloric_spatial_mono measurableSet_Ioo
    (c17_isOpen_sourceBall (0 : Vec d) R).measurableSet hspace
    (c13_weighted_caloric_time_mono measurableSet_Ioo
      (c17_isOpen_sourceBall (0 : Vec d) R).measurableSet htime hcal)
  have hnorm : 0 ≤ euclideanNorm (y-x) := Real.sqrt_nonneg _
  have hsmall : euclideanNorm (y-x) < r/2 := by nlinarith [sq_nonneg (euclideanNorm (y-x) + r/2)]
  let w : Vec d := r⁻¹ • (y-x)
  have hw : w ∈ sourceBall (0 : Vec d) (1/2) := by
    change euclideanNorm (w-0) < (1/2 : ℝ)
    simp only [sub_zero, w, TimeChange.euclideanNorm_smul, abs_of_pos (inv_pos.mpr hr)]
    rw [inv_mul_lt_iff₀ hr]
    linarith
  have hp : ((-5/8 : ℝ), (0 : Vec d)) ∈
      Set.Ioo (-11/16 : ℝ) (-9/16) ×ˢ sourceBall 0 (1/4) := by
    constructor
    · norm_num
    · change euclideanNorm ((0 : Vec d)-0) < (1/4 : ℝ)
      simp [euclideanNorm, euclideanSq, dot]
  have hq : ((5/8 : ℝ), w) ∈
      Set.Ioo (1/2 : ℝ) (3/4) ×ˢ sourceBall 0 (1/2) := ⟨by norm_num, hw⟩
  have hv := hscaled t₀ x r hr ρ α hell v G hcal' (hcont.mono hsub)
    (fun z hz => hnonneg z (hsub hz)) _ hp _ hq
  have hsp : x+r • (0 : Vec d) = x := by simp
  have hsq : x+r • w = y := by
    dsimp [w]
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul, add_sub_cancel]
  have htp : t₀+r^2*(-5/8) = s := by dsimp [t₀]; rw [hr2]; ring
  have htq : t₀+r^2*(5/8) = s+δ := by dsimp [t₀]; rw [hr2]; ring
  simpa only [hsp, hsq, htp, htq] using hv

end EinsteinFull.Calculus

