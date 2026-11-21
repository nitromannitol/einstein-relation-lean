import EinsteinFull.External.DFGW.RescaledTightness
import EinsteinFull.External.DFGW.DFGWFDD
import EinsteinFull.External.DFGW.ContinuousPathConvergence
import EinsteinFull.External.DFGW.ContinuousPathTests

/-! # The De Masi–Ferrari–Goldstein–Wick invariance principle

Proof of `EinsteinFull.External.Draft.dfgwInvarianceStmtV2` (De Masi, Ferrari, Goldstein and Wick,
J. Stat. Phys. 55 (1989), Theorem 2.2 with Remarks 1 and 3). The covariance formula, the scaled
second moments and the finite-dimensional Brownian limits come from the Kipnis–Varadhan
martingale approximation and the martingale central limit theorem; tightness of the rescaled
path laws comes from the uniform remainder estimate of the martingale approximation (source
(2.68)) and Doob's inequality for the stationary-increment martingale. Tightness and
finite-dimensional convergence give convergence against bounded continuous functionals of
continuous paths, and the limit has continuous paths, so the Skorokhod tests converge.

Departures from the source: the source proves tightness in the Skorokhod space through its
Lemma 2.6 and the maximal inequality for reversible processes; here the paths are continuous,
tightness is proved in the space of continuous paths by a block criterion with uniform
integrability of the normalized martingale increments, and the reversible maximal inequality is
used only for the resolvent boundary term.
-/

open MeasureTheory ProbabilityTheory Filter EinsteinRelation MarkovProcess
open scoped NNReal ENNReal Topology

namespace EinsteinFull.External.DFGW

/-- Finite-dimensional limits indexed by finite sets of times follow from those indexed by
`Fin m`. -/
theorem tendsto_integral_finsetEvaluation_of_fdd {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ} (Y : Ω → Path d) (W : Measure (Path d))
    [IsProbabilityMeasure W]
    (hfdd : ∀ (m : ℕ) (t : Fin m → ℝ≥0),
      TendstoInDistribution (fun (ε : ℝ) ω j => ε • Y ω ((ε⁻¹ ^ 2).toNNReal * t j))
        (𝓝[>] 0) (fun γ : Path d => fun j => γ (t j)) (fun _ => P) W)
    (I : Finset ℝ≥0) (g : BoundedContinuousFunction (I → Vec d) ℝ) :
    Tendsto (fun ε : ℝ => ∫ ω, g (fun i : I => ε • Y ω ((ε⁻¹ ^ 2).toNNReal * i)) ∂P)
      (𝓝[>] 0) (𝓝 (∫ γ, g (fun i : I => γ i) ∂W)) := by
  let e : I ≃ Fin I.card := I.equivFin
  let t : Fin I.card → ℝ≥0 := fun j => (e.symm j : ℝ≥0)
  let R : C(Fin I.card → Vec d, I → Vec d) :=
    ⟨fun x i => x (e i), continuous_pi fun i => continuous_apply (e i)⟩
  let g' : BoundedContinuousFunction (Fin I.card → Vec d) ℝ := g.compContinuous R
  have hconv := hfdd I.card t
  have h := (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
    hconv.forall_aemeasurable hconv.aemeasurable_limit).1 hconv g'
  have hg' (x : Fin I.card → Vec d) : g' x = g (fun i => x (e i)) := rfl
  simp only [hg', t, Equiv.symm_apply_apply] at h
  exact h

/-- **The De Masi–Ferrari–Goldstein–Wick invariance principle** (Theorem 2.2 with Remarks 1
and 3), in the form `EinsteinFull.External.Draft.dfgwInvarianceStmtV2`. -/
theorem dfgw_invariance_holds : EinsteinFull.External.Draft.dfgwInvarianceStmtV2 := by
  intro d S _ _ _ _ P μ T X Y hP hcoord _ hX φ hφ hlim hL2 hM
  let : IsProbabilityMeasure P := hP.probability
  obtain ⟨C, D, _, _, hCquad, hentries, _, hvariance, W, hW, hfdd⟩ :=
    exists_diffusion_matrix_fdd hP hcoord hX φ hφ hlim hL2 hM
  refine ⟨C, D, hCquad, hentries, hvariance, W, hW, ?_⟩
  let : IsProbabilityMeasure W := hW.1
  have hY : Measurable Y := hX.version_measurable
  have hY0 : ∀ᵐ η ∂P, Y η 0 = 0 := by
    filter_upwards [hX.version, hX.additive 0 0 0 le_rfl le_rfl] with η hv ha
    rw [hv 0]
    simp only [NNReal.coe_zero] at ha ⊢
    simpa using ha
  have hosc : ∀ (i : Fin d) {L ρ κ : ℝ}, 1 ≤ L → 0 < ρ → 0 < κ →
      ∃ δ : ℝ, 0 < δ ∧ ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₁ →
        P.real {η | ∃ s t : ℝ≥0, (s : ℝ) ≤ L ∧ (t : ℝ) ≤ L ∧ |(s : ℝ) - t| ≤ δ ∧
          ρ < |rescalePath ε (Y η) s i - rescalePath ε (Y η) t i|} ≤ κ := by
    intro i L ρ κ hL hρ hκ
    have hdot (v : Vec d) : dot (Pi.single i 1) v = v i := by
      simp [dot, Pi.single_apply]
    obtain ⟨δ, hδ, ε₁, hε₁, hε₁1, h⟩ := exists_scale_measureReal_oscillation_le hP hcoord hX φ
      hφ hlim hL2 hM hW hvariance hfdd (Pi.single i 1) hL hρ hκ
    refine ⟨δ, hδ, ε₁, hε₁, hε₁1, fun ε hε hεε₁ => ?_⟩
    simpa only [hdot] using h ε hε hεε₁
  have htight := exists_isCompact_rescaled_laws hY hY0 hosc W hW.2.2.2.1
  apply tendsto_skorokhod_of_boundedContinuous
  intro G
  let Q : ℝ → ProbabilityMeasure (Path d) := fun ε =>
    ⟨P.map (fun η => rescalePath ε (Y η)),
      (Measure.isProbabilityMeasure_map_iff
        (measurable_rescalePath_comp hY ε).aemeasurable).2 inferInstance⟩
  let W' : ProbabilityMeasure (Path d) := ⟨W, inferInstance⟩
  have hT : ∀ δ : ℝ, 0 < δ → ∃ K : Set (Path d), IsCompact K ∧
      (W' : Measure (Path d)) Kᶜ ≤ ENNReal.ofReal δ ∧
      ∀ᶠ ε in 𝓝[>] 0, (Q ε : Measure (Path d)) Kᶜ ≤ ENNReal.ofReal δ := htight
  have hFD (I : Finset ℝ≥0) (g : BoundedContinuousFunction (I → Vec d) ℝ) :
      Tendsto (fun ε => ∫ γ, g (ContinuousPath.finsetEvaluation I γ) ∂(Q ε : Measure (Path d)))
        (𝓝[>] 0)
        (𝓝 (∫ γ, g (ContinuousPath.finsetEvaluation I γ) ∂(W' : Measure (Path d)))) := by
    have h := tendsto_integral_finsetEvaluation_of_fdd Y W hfdd I g
    apply h.congr'
    filter_upwards with ε
    change (∫ η, g (fun i : I => ε • Y η ((ε⁻¹ ^ 2).toNNReal * i)) ∂P) =
      ∫ γ, g (ContinuousPath.finsetEvaluation I γ) ∂P.map (fun η => rescalePath ε (Y η))
    rw [integral_map (measurable_rescalePath_comp hY ε).aemeasurable]
    · rfl
    · exact (g.continuous.comp (ContinuousPath.continuous_finiteEvaluation _)).aestronglyMeasurable
  have h := tendsto_path_integral_of_tight_of_finiteDimensional Q W' hT hFD G
  apply h.congr'
  filter_upwards with ε
  change (∫ γ, G γ ∂P.map (fun η => rescalePath ε (Y η))) = _
  exact integral_map (measurable_rescalePath_comp hY ε).aemeasurable
    G.continuous.aestronglyMeasurable

end EinsteinFull.External.DFGW
