import EinsteinRelation.Correctors.FundamentalPositiveRepresentative

/-! # Positive-time representatives preserve the full E.1 contract

Source: `paper/main.tex:777–784,842`; AKM Proposition E.1. Only the
positive-time scalar kernel enters the contract, including its tested
mixed derivative. Values at other times may therefore be set to zero.
-/

open MeasureTheory Filter
open scoped Topology

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The mixed-derivative identity uses only positive-time kernel values.
Source: `paper/main.tex:777–784,842`; AKM (E.9). -/
theorem heatKernelMixedDerivative_congr_positive {d : ℕ}
    {P Q : ℝ → Vec d → Vec d → ℝ}
    {H : ℝ → Vec d → Vec d → Mat d}
    (hP : IsHeatKernelMixedDerivative P H)
    (hPQ : ∀ t, 0 < t → ∀ x y, P t x y = Q t x y) :
    IsHeatKernelMixedDerivative Q H := by
  refine ⟨hP.1, ?_⟩
  intro ψ hψ hψc hψs i j
  rw [← hP.2 ψ hψ hψc hψs i j]
  apply integral_congr_ae
  apply ae_of_all
  intro z
  dsimp only
  by_cases ht : 0 < z.1
  · rw [hPQ z.1 ht]
  · have hz : z ∉ tsupport ψ := fun hz => ht (hψs hz).1
    have hsub : tsupport (fun w => fderiv ℝ ψ w (0, (0, unitVector j))) ⊆
        tsupport ψ := by
      apply closure_minimal ?_ isClosed_closure
      intro w hw
      apply support_fderiv_subset ℝ
      intro hw0
      exact hw (by change (fderiv ℝ ψ w) (0, (0, unitVector j)) = 0; rw [hw0]; rfl)
    have hD := fderiv_of_notMem_tsupport (𝕜 := ℝ) (fun h => hz (hsub h))
    rw [hD]
    simp only [ContinuousLinearMap.zero_apply, mul_zero]

/-- Every clause of the E.1 kernel contract is invariant under changing
scalar values at nonpositive times. Source: `paper/main.tex:777–784,842`. -/
theorem heatKernelProperties_congr_positive {d : ℕ} {K : ℝ}
    {A : Coefficient d K} {P Q : ℝ → Vec d → Vec d → ℝ}
    {X Y : ℝ → Vec d → Vec d → Vec d}
    {H : ℝ → Vec d → Vec d → Mat d} {C : ℝ → ℝ}
    (hP : HeatKernelProperties A P X Y H C)
    (hPQ : ∀ t, 0 < t → ∀ x y, P t x y = Q t x y) :
    HeatKernelProperties A Q X Y H C := by
  rcases hP with ⟨hc, hp, hX, hY, hsym, hmass, hmix, hbound, htrace⟩
  refine ⟨hc.congr (fun z hz => (hPQ z.1 hz.1 z.2.1 z.2.2).symm),
    ?_, ?_, ?_, ?_, ?_, heatKernelMixedDerivative_congr_positive hmix hPQ,
    ?_, ?_⟩
  · intro t ht x y
    rw [← hPQ t ht x y]
    exact hp t ht x y
  · intro y
    exact fundamentalSolution_scalar_congr_positive (hX y) (fun t ht x => hPQ t ht x y)
  · intro x
    exact fundamentalSolution_scalar_congr_positive (hY x) (fun t ht y => hPQ t ht x y)
  · intro t ht x y
    rw [← hPQ t ht x y, ← hPQ t ht y x]
    exact hsym t ht x y
  · intro t ht x
    have heq : P t = Q t := funext fun x => funext fun y => hPQ t ht x y
    rw [← heq]
    exact hmass t ht x
  · intro α hα hαK t ht x y
    simpa only [← hPQ t ht] using hbound α hα hαK t ht x y
  · intro f hf y hfg hfy
    apply (htrace f hf y hfg hfy).congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [← hPQ t ht]

end EinsteinRelation.Correctors
