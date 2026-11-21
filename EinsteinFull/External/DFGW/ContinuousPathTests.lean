import EinsteinFull.Calculus.CLSkorokhod

/-! # Skorokhod tests restricted to continuous paths

A bounded Skorokhod test restricts to a bounded continuous function on continuous path space.
Consequently, convergence against bounded continuous tests on continuous paths implies
convergence against the Skorokhod tests used in the invariance statement.
-/

open MeasureTheory Filter EinsteinRelation
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

/-- The restriction of a bounded Skorokhod test to continuous paths is bounded and continuous. -/
theorem exists_boundedContinuous_restrict_skorokhod {d : ℕ}
    (F : Draft.CadlagPath d → ℝ) (hF : Draft.IsSkorokhodTest F) :
    ∃ G : BoundedContinuousFunction (Path d) ℝ,
      ∀ γ, G γ = F (Draft.Path.toCadlag γ) := by
  obtain ⟨⟨C, hC⟩, hseq⟩ := hF
  have hc : Continuous (fun γ : Path d => F (Draft.Path.toCadlag γ)) := by
    apply continuous_iff_seqContinuous.2
    intro γ γ₀ hγ
    exact hseq (fun n => Draft.Path.toCadlag (γ n)) (Draft.Path.toCadlag γ₀)
      (Draft.skorokhodTendsto_toCadlag_of_tendsto hγ)
  let G : BoundedContinuousFunction (Path d) ℝ :=
    BoundedContinuousFunction.mkOfBound ⟨fun γ => F (Draft.Path.toCadlag γ), hc⟩ (2 * C) (by
      intro γ γ'
      change dist (F (Draft.Path.toCadlag γ)) (F (Draft.Path.toCadlag γ')) ≤ 2 * C
      rw [Real.dist_eq]
      calc
        _ ≤ |F (Draft.Path.toCadlag γ)| + |F (Draft.Path.toCadlag γ')| := abs_sub _ _
        _ ≤ C + C := add_le_add (hC _) (hC _)
        _ = _ := by ring)
  exact ⟨G, fun _ => rfl⟩

/-- Weak convergence tested on continuous paths implies the Skorokhod-test convergence required
for laws supported on continuous paths. -/
theorem tendsto_skorokhod_of_boundedContinuous {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Y : Ω → Path d} {W : Measure (Path d)}
    (h : ∀ G : BoundedContinuousFunction (Path d) ℝ,
      Tendsto (fun ε : ℝ => ∫ η, G (rescalePath ε (Y η)) ∂P) (𝓝[>] 0)
        (𝓝 (∫ γ, G γ ∂W))) :
    ∀ F : Draft.CadlagPath d → ℝ, Draft.IsSkorokhodTest F →
      Tendsto (fun ε : ℝ => ∫ η, F (Draft.Path.toCadlag (rescalePath ε (Y η))) ∂P)
        (𝓝[>] 0) (𝓝 (∫ γ, F (Draft.Path.toCadlag γ) ∂W)) := by
  intro F hF
  obtain ⟨G, hG⟩ := exists_boundedContinuous_restrict_skorokhod F hF
  simpa only [hG] using h G

end EinsteinFull.External.DFGW
