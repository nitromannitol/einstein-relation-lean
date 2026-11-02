import EinsteinFull.Calculus.S3TailSumCore
import EinsteinFull.Blueprint.G1.node_p_u3A_tail_u23_sum
import EinsteinFull.Blueprint.Roots.node_rt_u3A_local_u2D_mixing

/-!
# `p:tail#sum` from `p:tail#small-endpoints`, `p:tail#annuli`, `rt:local-mixing`

The pair bound is `rt:local-mixing` applied to the annulus increments (centered, real-local, in
`L^p` by `p:tail#annuli`) at observation radius `((n+1)+(m+1)) l / s`; the weighted sums are the
sums of `p:tail#annuli`; the identification of the pair series with the correlation `K` is the
`L²` Lévy theorem plus the identity `K = ∫ F · P(t - 2T) G` of `p:tail#small-endpoints`. The
`rt:remainder-moment` hypothesis is not used.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace EinsteinFull.Blueprint

open EinsteinRelation EinsteinFull EinsteinFull.AnnuliSupport

theorem p_tail_sum_of_smallEndpoints
    (hsmall : node_p_u3A_tail_u23_small_u2D_endpointsStmt)
    (hann : node_p_u3A_tail_u23_annuliStmt)
    (hlm : node_rt_u3A_local_u2D_mixingStmt) :
    node_p_u3A_tail_u23_sumStmt := by
  intro d hd D
  obtain ⟨lm, pm, cm, Cm, lam₀m, hlm0, hlmr, hpm, hcm, hCm, hlam0m, hlam01, hmixQ⟩ :=
    hlm d hd D.ellipticity D.dependenceRange
  obtain ⟨l₀, ca, N, hl₀, hl₀r, hca, hann2⟩ := hann d hd D
  obtain ⟨Cs, hCs, hsQ⟩ := hsmall d hd D pm hpm
  obtain ⟨l, hldef⟩ : ∃ l : ℝ, l = max lm l₀ := ⟨_, rfl⟩
  have hlml : lm ≤ l := by rw [hldef]; exact le_max_left _ _
  have hl₀l : l₀ ≤ l := by rw [hldef]; exact le_max_right _ _
  have hlpos : 0 < l := lt_of_lt_of_le hlm0 hlml
  obtain ⟨Ca, C₁, C₂, hCa, hC₁, hC₂, hannQ⟩ :=
    hann2 l pm (Cm * l) hl₀l hpm (mul_pos hCm hlpos).le
  refine ⟨l, pm, Cm * Ca ^ 2 + 2 * Ca + 2 * cm + Cm + Cm * l, cm, 2,
    min lam₀m (Real.exp (-1)), hlpos, by linarith, hpm, by positivity, hcm, le_refl _,
    lt_min hlam0m (Real.exp_pos _), min_le_right _ _, ?_⟩
  intro Q hQ β a μ hβ ha hμ lam hlam hlam₀ P Pdag hP hPd
  haveI := reducedLaw_probability Q
  intro s T h F j velocity G E Δ normp t ht pair K
  have hs : 0 < |lam| := hlam
  have hs1 : |lam| ≤ Real.exp (-1) := hlam₀.trans (min_le_right _ _)
  have hsm : |lam| ≤ lam₀m := hlam₀.trans (min_le_left _ _)
  have hTdef : ((T : ℝ≥0) : ℝ) = (s ^ 2)⁻¹ := Real.coe_toNNReal _ (by positivity)
  have hT : (T : ℝ) * |lam| ^ 2 = 1 := by
    rw [hTdef]; exact inv_mul_cancel₀ (pow_ne_zero 2 hs.ne')
  have h2Tr : 2 * (T : ℝ) ≤ (t : ℝ) := by
    rw [hTdef]
    calc 2 * (s ^ 2)⁻¹ = 2 / s ^ 2 := by ring
      _ ≤ (t : ℝ) := ht
  have h2T : 2 * T ≤ t := by
    apply NNReal.coe_le_coe.1
    push_cast
    exact h2Tr
  obtain ⟨-, -, -, -, -, hKid'⟩ := hsQ Q hQ β a μ hβ ha hμ lam hlam hs1 P Pdag hP hPd j velocity
  have hKid := hKid' t h2T
  have hA := hannQ Q hQ β a μ hβ ha hμ lam hlam hs1 P Pdag hP hPd j velocity
  have hAF := hA F (Set.mem_insert _ _)
  have hAG := hA G (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hFA : AnnData Q l |lam| pm (Cm * l) Ca h F := by
    obtain ⟨-, hΔ, hsum, htsum, -⟩ := hAF
    exact ⟨fun n hn => ⟨(hΔ n hn).1, (hΔ n hn).2.1, (hΔ n hn).2.2.1⟩, hsum, htsum⟩
  have hGA : AnnData Q l |lam| pm (Cm * l) Ca h G := by
    obtain ⟨-, hΔ, hsum, htsum, -⟩ := hAG
    exact ⟨fun n hn => ⟨(hΔ n hn).1, (hΔ n hn).2.1, (hΔ n hn).2.2.1⟩, hsum, htsum⟩
  have hh2 : 2 * h = (d : ℝ) + 2 := by
    show 2 * (1 + (d : ℝ) / 2) = (d : ℝ) + 2
    ring
  have core := tail_sum_core Q lam l pm lm Cm cm Ca
    (Cm * Ca ^ 2 + 2 * Ca + 2 * cm + Cm + Cm * l) h hlpos hlml hCm hcm hCa hs hs1 hh2
    (le_refl _) P T t hT h2T F G K hKid
    (fun A hA U V hU hV hUm hVm hU0 =>
      hmixQ Q lam hlam hsm P hP A hA U V hU hV hUm hVm hU0 (t - 2 * T))
    hFA hGA
  obtain ⟨c1, c2, c3, c4, c5⟩ := core
  refine ⟨c1, c2, c3, c4, hh2, ?_, c5⟩
  rw [mul_comm]
  exact hT

end EinsteinFull.Blueprint
