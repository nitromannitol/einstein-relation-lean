import EinsteinFull.Calculus.SunaS2Pathwise

open MeasureTheory ProbabilityTheory
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal Topology

namespace EinsteinFull
open EinsteinRelation EinsteinRelation.Regeneration

/-- Rational-time finite-dimensional distributions determine a continuous path law. -/
theorem s2_continuous_path_law_eq_of_rational_FDD
    {d : ℕ} (P Q : Measure (Path d)) [IsProbabilityMeasure Q]
    (h : ∀ I : Finset ℚ,
      P.map (fun γ : Path d => fun t : I => γ (Real.toNNReal ((t : ℚ) : ℝ))) =
      Q.map (fun γ : Path d => fun t : I => γ (Real.toNNReal ((t : ℚ) : ℝ)))) :
    P = Q := by
  classical
  let : StandardBorelSpace (MarkovProcess.ContinuousPath (Vec d)) :=
    MarkovProcess.ContinuousPath.standardBorelSpace_borel
  apply MarkovProcess.Measure.map_denseRestriction_injective (alpha := Vec d)
  let D := MarkovProcess.ContinuousPath.denseRestriction (alpha := Vec d)
  have hD : Measurable D := MarkovProcess.ContinuousPath.measurable_denseRestriction
  have hdense (J : Finset MarkovProcess.DenseTime) :
      P.map (fun γ => J.restrict (D γ)) = Q.map (fun γ => J.restrict (D γ)) := by
    let I : Finset ℚ := J.image (fun q : MarkovProcess.DenseTime => q.val)
    let r (x : I → Vec d) : J → Vec d := fun q =>
      x ⟨q.val.val, Finset.mem_image_of_mem _ q.property⟩
    have hr : Measurable r := Measurable.of_eval fun q => measurable_pi_apply _
    have he : Measurable (fun γ : Path d => fun t : I => γ (Real.toNNReal ((t : ℚ) : ℝ))) :=
      Measurable.of_eval fun t => (MarkovProcess.ContinuousPath.continuous_eval
        (alpha := Vec d) (Real.toNNReal ((t : ℚ) : ℝ))).measurable
    have hh := congrArg (fun R => R.map r) (h I)
    rw [Measure.map_map hr he, Measure.map_map hr he] at hh
    have hcast (q : MarkovProcess.DenseTime) :
        Real.toNNReal ((q : ℚ) : ℝ) = MarkovProcess.DenseTime.castOrderEmbedding q := by
      rcases q with ⟨q, hq⟩
      change Real.toNNReal (q : ℝ) = NNRat.cast (K := ℝ≥0) ⟨q, hq⟩
      symm
      apply NNReal.eq
      rw [Real.coe_toNNReal _ (Rat.cast_nonneg.mpr hq)]
      norm_cast
    have hfun : (fun γ : Path d => J.restrict (D γ)) =
        (r ∘ fun γ : Path d => fun t : I => γ (Real.toNNReal ((t : ℚ) : ℝ))) := by
      funext γ q
      change γ (MarkovProcess.DenseTime.castOrderEmbedding q) =
        γ (Real.toNNReal (((q : MarkovProcess.DenseTime) : ℚ) : ℝ))
      rw [hcast]
    rw [← hfun] at hh
    exact hh
  have hp := ProbabilityTheory.isProjectiveLimit_map (P := P) hD.aemeasurable
  have hq := ProbabilityTheory.isProjectiveLimit_map (P := Q) hD.aemeasurable
  change IsProjectiveLimit (P.map D) (fun J => P.map (fun γ => J.restrict (D γ))) at hp
  change IsProjectiveLimit (Q.map D) (fun J => Q.map (fun γ => J.restrict (D γ))) at hq
  simp_rw [hdense] at hp
  exact hp.unique hq


/-- Rational finite-dimensional laws of the supplied stopped paths determine their laws. -/
theorem s2_supplied_stopped_law_eq_of_rational_FDD
    {d : ℕ} (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (ω ω' : FieldPair d) (hω : IsRegular Λ ω) (hω' : IsRegular Λ ω')
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (r : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (r' : GantertFixedEnvironmentRealization hd Λ hΛ ω' hω' lam h0 h1)
    (U : Set (Vec d)) (x : Vec d)
    (h : ∀ I : Finset ℚ,
      ((r.pathLaw x).map (Diffusion.localityStoppedPath U)).map
        (fun γ : Path d => fun t : I => γ (Real.toNNReal ((t : ℚ) : ℝ))) =
      ((r'.pathLaw x).map (Diffusion.localityStoppedPath U)).map
        (fun γ : Path d => fun t : I => γ (Real.toNNReal ((t : ℚ) : ℝ)))) :
    (r.pathLaw x).map (Diffusion.localityStoppedPath U) =
      (r'.pathLaw x).map (Diffusion.localityStoppedPath U) := by
  letI : IsMarkovKernel r.pathLaw := r.pathLaw_isMarkovKernel
  letI : IsMarkovKernel r'.pathLaw := r'.pathLaw_isMarkovKernel
  letI := isProbabilityMeasure_map_localityStoppedPath U (r.pathLaw x)
  letI := isProbabilityMeasure_map_localityStoppedPath U (r'.pathLaw x)
  exact s2_continuous_path_law_eq_of_rational_FDD _ _ h


theorem s2_shifted_future_supplied_stopped_locality_of_killed_fdd (hk : S2SuppliedKilledFDDLocality)
    {d : ℕ}
    (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ}
    (hΛ₀ : 1 ≤ Λ₀)
    (Q : EnvironmentLaw d Λ₀ r₀)
    (lam l δ : ℝ)
    (hl : 0 < l)
    (h0 : 0 < lam)
    (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d)
    (K : CoupledQuenchedLaws d)
    (_hK : Renewal.IsGMPCouplingV2 hd hΛ₀ Q lam l δ h0.le h1 P K)
    : let R := l / lam;
    let i := Renewal.forceCoord hd;
    let Δ := Renewal.regenDelta lam;
    ∀ (a : Vec d) (ω ω' : FieldPair d)
    (hω : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω))
    (hω' : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω'))
    (r : External.GantertSection7Support.GantertFixedEnvironmentRealization hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀) (zeroPotentialReducedPair ω) hω lam h0.le h1)
    (r' : External.GantertSection7Support.GantertFixedEnvironmentRealization hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀) (zeroPotentialReducedPair ω') hω' lam h0.le h1), (∀ y : Vec d, P (y, ω) = r.pathLaw y)
    → (∀ y : Vec d, P (y, ω') = r'.pathLaw y)
    → (∀ y : Vec d, a i - 2 * R ≤ y i → ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y)
    → ∀ y : Vec d, a i - R ≤ y i → (P (y, ω)).map (Diffusion.localityStoppedPath {x : Vec d | a i - 2 * R < x i}) = (P (y, ω')).map (Diffusion.localityStoppedPath {x : Vec d | a i - 2 * R < x i}) := by
  dsimp only
  intro a ω ω' hω hω' r r' hp hp' hfields y hy
  have hR : 0 < l / lam := div_pos hl h0
  rw [hp y, hp' y]
  apply s2_supplied_stopped_locality_of_generic_killed_fdd hk hd _ _ _ _ hω hω' lam h0.le h1 r r'
  · exact isOpen_lt continuous_const (continuous_apply _)
  · intro z hz
    have he := hfields z (le_of_lt hz)
    simp [reducedCoefficient, clockDensity, he.1, he.2]
  · dsimp
    linarith


theorem s2_future_supplied_stopped_locality_of_killed_fdd (hk : S2SuppliedKilledFDDLocality)
    {d : ℕ}
    (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ}
    (hΛ₀ : 1 ≤ Λ₀)
    (Q : EnvironmentLaw d Λ₀ r₀)
    (lam l δ : ℝ)
    (hl : 0 < l)
    (h0 : 0 < lam)
    (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d)
    (K : CoupledQuenchedLaws d)
    (_hK : Renewal.IsGMPCouplingV2 hd hΛ₀ Q lam l δ h0.le h1 P K)
    : let R := l / lam;
    let i := Renewal.forceCoord hd;
    let Δ := Renewal.regenDelta lam;
    ∀ (ω ω' : FieldPair d)
    (hω : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω))
    (hω' : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω'))
    (r : External.GantertSection7Support.GantertFixedEnvironmentRealization hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀) (zeroPotentialReducedPair ω) hω lam h0.le h1)
    (r' : External.GantertSection7Support.GantertFixedEnvironmentRealization hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀) (zeroPotentialReducedPair ω') hω' lam h0.le h1), (∀ y : Vec d, P (y, ω) = r.pathLaw y)
    → (∀ y : Vec d, P (y, ω') = r'.pathLaw y)
    → (∀ y : Vec d, -2 * R ≤ y i → ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y)
    → ∀ y : Vec d, -R ≤ y i → (P (y, ω)).map (Diffusion.localityStoppedPath {x : Vec d | -2 * R < x i}) = (P (y, ω')).map (Diffusion.localityStoppedPath {x : Vec d | -2 * R < x i}) := by
  dsimp only
  intro ω ω' hω hω' r r' hp hp' hfields y hy
  have hR : 0 < l / lam := div_pos hl h0
  rw [hp y, hp' y]
  apply s2_supplied_stopped_locality_of_generic_killed_fdd hk hd _ _ _ _ hω hω' lam h0.le h1 r r'
  · exact isOpen_lt continuous_const (continuous_apply _)
  · intro z hz
    have he := hfields z (le_of_lt hz)
    simp [reducedCoefficient, clockDensity, he.1, he.2]
  · dsimp
    linarith


theorem s2_past_supplied_stopped_locality_of_killed_fdd (hk : S2SuppliedKilledFDDLocality)
    {d : ℕ}
    (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ}
    (hΛ₀ : 1 ≤ Λ₀)
    (Q : EnvironmentLaw d Λ₀ r₀)
    (lam l δ : ℝ)
    (hl : 0 < l)
    (h0 : 0 < lam)
    (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d)
    (K : CoupledQuenchedLaws d)
    (_hK : Renewal.IsGMPCouplingV2 hd hΛ₀ Q lam l δ h0.le h1 P K)
    (v : ℝ)
    : let R := l / lam;
    let i := Renewal.forceCoord hd;
    let Δ := Renewal.regenDelta lam;
    ∀ (ω ω' : FieldPair d)
    (hω : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω))
    (hω' : IsRegular (sourceReducedBound Λ₀) (zeroPotentialReducedPair ω'))
    (r : External.GantertSection7Support.GantertFixedEnvironmentRealization hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀) (zeroPotentialReducedPair ω) hω lam h0.le h1)
    (r' : External.GantertSection7Support.GantertFixedEnvironmentRealization hd (sourceReducedBound Λ₀) (one_le_sourceReducedBound hΛ₀) (zeroPotentialReducedPair ω') hω' lam h0.le h1), (∀ y : Vec d, P (y, ω) = r.pathLaw y)
    → (∀ y : Vec d, P (y, ω') = r'.pathLaw y)
    → (∀ y : Vec d, y i ≤ v + 3 * R → ω.1 y = ω'.1 y ∧ ω.2 y = ω'.2 y)
    → ∀ y : Vec d, y i ≤ v → (r.pathLaw y).map (Diffusion.localityStoppedPath {x : Vec d | x i < v + 3 * R}) = (r'.pathLaw y).map (Diffusion.localityStoppedPath {x : Vec d | x i < v + 3 * R}) := by
  dsimp only
  intro ω ω' hω hω' r r' hp hp' hfields y hy
  have hR : 0 < l / lam := div_pos hl h0
  apply s2_supplied_stopped_locality_of_generic_killed_fdd hk hd _ _ _ _ hω hω' lam h0.le h1 r r'
  · exact isOpen_lt (continuous_apply _) continuous_const
  · intro z hz
    have he := hfields z (le_of_lt hz)
    simp [reducedCoefficient, clockDensity, he.1, he.2]
  · dsimp
    linarith


end EinsteinFull
