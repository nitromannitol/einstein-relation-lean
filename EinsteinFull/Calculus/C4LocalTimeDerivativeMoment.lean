import EinsteinFull.Blueprint.Foundation.node_e_u3A_local_u2D_time
import EinsteinFull.Blueprint.Foundation.node_l_u3A_forced_u2D_local_u23_centered_u2D_source
import EinsteinFull.Blueprint.Foundation.node_e_u3A_lp_u2D_growth
import EinsteinFull.Calculus.C4PhysicalLocalEnergy
import EinsteinFull.Calculus.LocalEnergySupport
import EinsteinFull.Calculus.MigrationMeasurabilitySupport
import EinsteinFull.Calculus.C1EndpointFiniteP
import EinsteinRelation.Correctors.NormBallVolumeBound
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull
/-- The derivative moment estimate uses genuine endpoint witnesses at every
positive time. This construction does not use a moment estimate. -/
theorem local_time_endpoint_witnesses
    {d : ℕ} (hd : 2 ≤ d) {D : StructuralData d}
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β)
    (ha : IsReducedCoefficientObservation Q a)
    (hμ : IsReducedClockObservation Q μ) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag) (ν : EndpointIndex d) :
    ∃ G : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
    ∃ V : ℝ≥0 → Lp ℂ 2 (reducedLaw Q),
      ∀ t : ℝ≥0, 0 < (t : ℝ) →
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (indexedEndpoint hd Q ν ζ P Pdag β a μ t) (G t) ∧
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (uncenteredEndpoint hd Q ν ζ P Pdag β a μ t) (G t) ∧
        HasDerivAt (fun r : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ r.toNNReal)
          (V t) (t : ℝ) := by
  let := reducedLaw_probability Q
  have hw (t : ℝ≥0) (ht : 0 < (t : ℝ)) :
      ∃ (G : Fin d → Lp ℂ 2 (reducedLaw Q)) (V : Lp ℂ 2 (reducedLaw Q)),
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (indexedEndpoint hd Q ν ζ P Pdag β a μ t) G ∧
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (uncenteredEndpoint hd Q ν ζ P Pdag β a μ t) G ∧
        HasDerivAt (fun r : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ r.toNNReal)
          V (t : ℝ) := by
    obtain ⟨G, J, V, hflux, hder, _⟩ :=
      node_e_u3A_centered_u2D_equations_of_deps d hd D Q hQ β a μ hβ ha hμ
        ζ P Pdag hP hPdag ν t ht
    refine ⟨G, V, hflux.1, ?_, hder⟩
    cases ν with
    | inl k =>
      intro j
      have hc := hasComplexHorizontalGradient_const (reducedLaw Q)
        (reducedLaw_stationary Q)
        (∫ ω, (P t (β k + ζ • a ⟨0, by omega⟩ k)) ω ∂reducedLaw Q)
      simpa only [indexedEndpoint, velocityEndpoint, centeredComplexLp,
        sub_add_cancel, add_zero, uncenteredEndpoint] using (hflux.1 j).add (hc j)
    | inr b =>
      cases b with
      | true => exact hflux.1
      | false =>
        have he : centeredComplexLp Q (ζ • P t μ) =
            indexedEndpoint hd Q (.inr false) ζ P Pdag β a μ t := by
          rw [← centeredComplexLpCLM_apply, map_smul, centeredComplexLpCLM_apply]
          rfl
        have hg := hflux.1
        rw [← he] at hg
        intro j
        have hc := hasComplexHorizontalGradient_const (reducedLaw Q)
          (reducedLaw_stationary Q) (∫ ω, (ζ • P t μ) ω ∂reducedLaw Q)
        simpa only [centeredComplexLp, sub_add_cancel, add_zero, uncenteredEndpoint]
          using (hg j).add (hc j)
  choose G V hspec using hw
  exact ⟨fun t => if ht : 0 < (t : ℝ) then G t ht else 0,
    fun t => if ht : 0 < (t : ℝ) then V t ht else 0,
    fun t ht => by simpa only [ht, ↓reduceDIte] using hspec t ht⟩

/-- The Lp-growth dependency supplies the literal earlier-time endpoint
integrability required by the derivative moment contract, including force zero. -/
theorem local_time_endpoint_memLp
    (h1 : node_e_u3A_lp_u2D_growthStmt)
    {d : ℕ} (hd : 2 ≤ d) {D : StructuralData d} (p : ℝ) (hp : 2 ≤ p)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β)
    (ha : IsReducedCoefficientObservation Q a)
    (hμ : IsReducedClockObservation Q μ) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    (ν : EndpointIndex d) (t : ℝ≥0) :
    MemLp (indexedEndpoint hd Q ν ζ P Pdag β a μ t)
      (ENNReal.ofReal p) (reducedLaw Q) := by
  let := reducedLaw_probability Q
  obtain ⟨C, _hC, hbound⟩ := h1 d D.ellipticity D.dependenceRange p hd hp
  have hgrowth := (hbound Q ⟨0, by omega⟩ ζ P Pdag hP hPdag).1
  obtain ⟨K, _hK, hobs⟩ := EndpointFiniteP.observation_bounds d D
  obtain ⟨hb, ha', hm⟩ := hobs Q hQ β a μ hβ ha hμ
  have hβp (j : Fin d) : MemLp (β j) (ENNReal.ofReal p) (reducedLaw Q) :=
    MemLp.of_bound (Lp.memLp (β j)).aestronglyMeasurable K (hb j)
  have hap (j k : Fin d) : MemLp (a j k) (ENNReal.ofReal p) (reducedLaw Q) :=
    MemLp.of_bound (Lp.memLp (a j k)).aestronglyMeasurable K (ha' j k)
  have hμp : MemLp μ (ENNReal.ofReal p) (reducedLaw Q) :=
    MemLp.of_bound (Lp.memLp μ).aestronglyMeasurable K hm
  have hsmul (f : Lp ℂ 2 (reducedLaw Q))
      (hf : MemLp f (ENNReal.ofReal p) (reducedLaw Q)) :
      MemLp (ζ • f) (ENNReal.ofReal p) (reducedLaw Q) :=
    (memLp_congr_ae (Lp.coeFn_smul ζ f)).2 (hf.const_smul ζ)
  have hcenter (f : Lp ℂ 2 (reducedLaw Q))
      (hf : MemLp f (ENNReal.ofReal p) (reducedLaw Q)) :
      MemLp (centeredComplexLp Q f) (ENNReal.ofReal p) (reducedLaw Q) :=
    (memLp_congr_ae (coeFn_centeredComplexLp Q f)).2 (hf.sub (memLp_const _))
  cases ν with
  | inl k =>
    have hinit : MemLp (β k + ζ • a ⟨0, by omega⟩ k)
        (ENNReal.ofReal p) (reducedLaw Q) :=
      (memLp_congr_ae (Lp.coeFn_add _ _)).2 ((hβp k).add (hsmul _ (hap _ k)))
    exact hcenter _ (hgrowth t _ hinit).1
  | inr b =>
    cases b with
    | false => exact hsmul _ (hcenter _ (hgrowth t μ hμp).1)
    | true => exact (hgrowth t _ (hβp ⟨0, by omega⟩)).2.1

/-- Joint representatives of the same time-dependent field give the same
physical field almost everywhere in environment and space-time. This is used
to compare independently constructed cutoff-energy witnesses. -/
theorem local_time_physical_representative_congr
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {W V : ℝ × FieldPair d → ℂ} (hW : Measurable W) (hV : Measurable V)
    (he : ∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] fun ω => V (s, ω)) :
    ∀ᵐ ω ∂reducedLaw Q,
      (fun p : ℝ × Vec d => W (p.1, translate p.2 ω)) =ᵐ[volume.prod volume]
        fun p => V (p.1, translate p.2 ω) := by
  have hmW := measurable_joint_spatial_translate hW
  have hmV := measurable_joint_spatial_translate hV
  have hephys : ∀ᵐ s ∂(volume : Measure ℝ),
      ∀ᵐ p ∂(volume : Measure (Vec d)).prod (reducedLaw Q),
        W (s, translate p.1 p.2) = V (s, translate p.1 p.2) := by
    apply ae_of_all
    intro s
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
      (hmW.comp (measurable_const.prodMk measurable_id))
      (hmV.comp (measurable_const.prodMk measurable_id)))).mpr
    exact ae_of_all _ fun x =>
      (measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) x).quasiMeasurePreserving.ae
        (he s)
  have heprod := (Measure.ae_prod_iff_ae_ae
    (measurableSet_eq_fun hmW hmV)).mpr hephys
  have heassoc := (measurePreserving_prodAssoc
    (volume : Measure ℝ) (volume : Measure (Vec d)) (reducedLaw Q)).quasiMeasurePreserving.ae heprod
  exact Measure.ae_ae_of_ae_prod
    (Measure.measurePreserving_swap.quasiMeasurePreserving.ae heassoc)

/-- Integrals of physical observables are independent of the chosen joint
representatives, including observables of countably many field components. -/
theorem local_time_physical_cylinder_integral_congr
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {κ : Type*} [Countable κ]
    {F H : κ → ℝ × FieldPair d → ℂ}
    (hF : ∀ j, Measurable (F j)) (hH : ∀ j, Measurable (H j))
    (he : ∀ j s, (fun ω => F j (s, ω)) =ᵐ[reducedLaw Q] fun ω => H j (s, ω))
    (Φ : (κ → ℂ) → ℝ) (J : Set ℝ) (S : Set (Vec d)) :
    ∀ᵐ ω ∂reducedLaw Q,
      (∫ s in J, ∫ x in S, Φ (fun j => F j (s, translate x ω))) =
        ∫ s in J, ∫ x in S, Φ (fun j => H j (s, translate x ω)) := by
  have hall : ∀ᵐ ω ∂reducedLaw Q, ∀ j,
      (fun p : ℝ × Vec d => F j (p.1, translate p.2 ω)) =ᵐ[volume.prod volume]
        fun p => H j (p.1, translate p.2 ω) :=
    ae_all_iff.mpr fun j => local_time_physical_representative_congr (hF j) (hH j) (he j)
  filter_upwards [hall] with ω hω
  have hjoint : ∀ᵐ p ∂(volume : Measure ℝ).prod (volume : Measure (Vec d)),
      ∀ j, F j (p.1, translate p.2 ω) = H j (p.1, translate p.2 ω) :=
    ae_all_iff.mpr hω
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hjoint)] with s hs
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hs] with x hx
  exact congrArg Φ (funext hx)

/-- The derivative Caccioppoli estimate holds for any measurable joint
representatives of the actual restarted derivative and its actual gradient.
Uniqueness identifies the restart datum from the energy construction. -/
theorem local_time_restarted_derivative_gapCaccioppoli
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f g : Lp ℂ 2 (reducedLaw Q)) {t a b : ℝ}
    (ht : 0 < t) (ha : 0 < a) (hab : a < b)
    (V : ℝ × FieldPair d → ℂ) (E : Fin d → ℝ × FieldPair d → ℂ)
    (hV : Measurable V) (hE : ∀ j, Measurable (E j))
    (heV : ∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] P (s - a).toNNReal g)
    (heE : ∀ j s, (fun ω => E j (s, ω)) =ᵐ[reducedLaw Q]
      (hP.gradientOrbit g (s - a)) j)
    (hg : ∀ r, a < r →
      HasDerivAt (fun s : ℝ =>
        centeredComplexLp Q (P s.toNNReal (centeredComplexLp Q f)) +
          Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..s, hP.centeringSource f v))
        (P (r - a).toNNReal g) r) :
    let L := Real.exp (2 * Λ₀) * Λ₀
    ∃ B T : ℝ, 0 < B ∧ 0 < T ∧
      ∀ c e v : ℝ, b < c → c < e → e ≤ v → ∀ z : Vec d, ∀ r R : ℝ,
        0 < r → r < R → ∀ᵐ ω ∂reducedLaw Q,
          (∫ s in Icc e v, ∫ x in {x | euclideanNorm (x - z) ≤ r},
            ∑ j, ‖E j (s, translate x ω)‖ ^ 2) ≤
          4 * L * (T / (e - c) / 2 +
            (2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3) *
              (‖ζ‖ ^ 2 + (d : ℝ) * B ^ 2 / (R - r) ^ 2)) *
            (∫ s in Icc c v, ∫ x in {x | euclideanNorm (x - z) ≤ R},
              ‖V (s, translate x ω)‖ ^ 2) := by
  intro L
  obtain ⟨B, T, hB, hT, g', h, V', Z, E', hV', hZ, hE', heV', heZ, heE',
    hw, hd, hlocal, hcacc⟩ :=
      complexForced_correctedOrbit_derivative_ae_gapCaccioppoli hP f ht ha hab
  have hgg : g' = g := hP.restart_derivative_unique (fun s hs => (hw s hs).1) hg
  subst g'
  refine ⟨B, T, hB, hT, ?_⟩
  intro c e v hc hce hev z r R hr hrR
  have hgrad := local_time_physical_cylinder_integral_congr hE hE'
    (fun j s => (heE j s).trans (heE' j s).symm)
    (fun u => ∑ j, ‖u j‖ ^ 2) (Icc e v) {x | euclideanNorm (x - z) ≤ r}
  have hmass := local_time_physical_cylinder_integral_congr
    (κ := Unit) (fun _ => hV) (fun _ => hV')
    (fun _ s => (heV s).trans (heV' s).symm)
    (fun u => ‖u ()‖ ^ 2) (Icc c v) {x | euclideanNorm (x - z) ≤ R}
  filter_upwards [hcacc c e v hc hce hev z r R hr hrR, hgrad, hmass]
    with ω hcacc hgrad hmass
  rw [hgrad, hmass]
  exact hcacc

/-- Original-orbit Caccioppoli on prescribed representatives, so its gradient
mass can be substituted directly into the output Young estimate. -/
theorem local_time_corrected_orbit_gapCaccioppoli
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t a : ℝ} (ht : 0 < t) (ha : 0 < a)
    (W : ℝ × FieldPair d → ℂ) (D : Fin d → ℝ × FieldPair d → ℂ)
    (hW : Measurable W) (hD : ∀ j, Measurable (D j))
    (heW : ∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q]
      (centeredComplexLp Q (P s.toNNReal (centeredComplexLp Q f)) +
        Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..s, hP.centeringSource f v) :
          Lp ℂ 2 (reducedLaw Q)))
    (heD : ∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q]
      (hP.gradientOrbit (centeredComplexLp Q f) s) j) :
    let L := Real.exp (2 * Λ₀) * Λ₀
    ∃ B T : ℝ, 0 < B ∧ 0 < T ∧
      ∀ b e c : ℝ, a < b → b < e → e ≤ c → ∀ z : Vec d, ∀ r R : ℝ,
        0 < r → r < R → ∀ᵐ ω ∂reducedLaw Q,
          (∫ s in Icc e c, ∫ x in {x | euclideanNorm (x - z) ≤ r},
            ∑ j, ‖D j (s, translate x ω)‖ ^ 2) ≤
          4 * L * (T / (e - b) / 2 +
            (2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3) *
              (‖ζ‖ ^ 2 + (d : ℝ) * B ^ 2 / (R - r) ^ 2)) *
            (∫ s in Icc b c, ∫ x in {x | euclideanNorm (x - z) ≤ R},
              ‖W (s, translate x ω)‖ ^ 2) := by
  intro L
  obtain ⟨B, T, hB, hT, g, W', V, D', hW', hV, hD', heW', heV, heD',
    hw, hcacc⟩ := complexForced_correctedOrbit_ae_physical_gapCaccioppoli hP f ht ha
  refine ⟨B, T, hB, hT, ?_⟩
  intro b e c hb hbe hec z r R hr hrR
  have hgrad := local_time_physical_cylinder_integral_congr hD hD'
    (fun j s => (heD j s).trans (heD' j s).symm)
    (fun u => ∑ j, ‖u j‖ ^ 2) (Icc e c) {x | euclideanNorm (x - z) ≤ r}
  have hmass := local_time_physical_cylinder_integral_congr
    (κ := Unit) (fun _ => hW) (fun _ => hW')
    (fun _ s => (heW s).trans (heW' s).symm)
    (fun u => ‖u ()‖ ^ 2) (Icc b c) {x | euclideanNorm (x - z) ≤ R}
  filter_upwards [hcacc b e c hb hbe hec z r R hr hrR, hgrad, hmass]
    with ω hcacc hgrad hmass
  rw [hgrad, hmass]
  exact hcacc

/-- Unweighted cylinder interpolation for the actual restarted derivative.
The original gradient and derivative gradient are the same joint fields used
by the corresponding Caccioppoli estimates above. -/
theorem local_time_corrected_orbit_outputMassInterpolation
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t a : ℝ} (ht : 0 < t) (ha : 0 < a) :
    let L := Real.exp (2 * Λ₀) * Λ₀
    let w := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
    ∃ B : ℝ, 0 < B ∧ ∃ g : Lp ℂ 2 (reducedLaw Q),
      ∃ W V : ℝ × FieldPair d → ℂ, ∃ D E : Fin d → ℝ × FieldPair d → ℂ,
      Measurable W ∧ Measurable V ∧ (∀ j, Measurable (D j)) ∧ (∀ j, Measurable (E j)) ∧
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] w s) ∧
      (∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] P (s - a).toNNReal g) ∧
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q]
        (hP.gradientOrbit (centeredComplexLp Q f) s) j) ∧
      (∀ j s, (fun ω => E j (s, ω)) =ᵐ[reducedLaw Q]
        (hP.gradientOrbit g (s - a)) j) ∧
      (∀ r, a < r → HasDerivAt w (P (r - a).toNNReal g) r ∧
        IsComplexGeneratorPair Q i ζ (w r) (P (r - a).toNNReal g)) ∧
      ∀ b c : ℝ, a < b → b ≤ c → ∀ z : Vec d, ∀ r R : ℝ,
        0 < r → r < R → ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂reducedLaw Q,
          (∫ s in Icc b c, ∫ x in {x | euclideanNorm (x - z) ≤ r},
            ‖V (s, translate x ω)‖ ^ 2) ≤
          2 * ε * (∫ s in Icc b c, ∫ x in {x | euclideanNorm (x - z) ≤ R},
            ∑ j, ‖E j (s, translate x ω)‖ ^ 2) +
          2 * ((1 / (4 * ε) + 4 * ((d : ℝ) * B ^ 2 / (R - r) ^ 2)) *
            ((d : ℝ) ^ 2 * L ^ 2 / 4) + ‖ζ‖ ^ 2 * ((d : ℝ) * L ^ 2)) *
            (∫ s in Icc b c, ∫ x in {x | euclideanNorm (x - z) ≤ R},
              ∑ j, ‖D j (s, translate x ω)‖ ^ 2) := by
  intro L w
  let := reducedLaw_probability Q
  obtain ⟨B, hB, hcutoff⟩ := exists_physical_gap_euclidean_cutoff d
  obtain ⟨g, W, V, D, E, hW, hV, hD, hE, heW, heV, heD, heE, hregular, hyoung⟩ :=
    complexForced_correctedOrbit_ae_physical_integratedOutputYoung hP f ht ha
  refine ⟨B, hB, g, W, V, D, E, hW, hV, hD, hE, heW, heV, heD, heE, hregular, ?_⟩
  intro b c hb hbc z r R hr hrR ε hε
  obtain ⟨φ, hφ, hφrange, hone, hzero, hφD⟩ := hcutoff z r R hr hrR
  let K := {x : Vec d | euclideanNorm (x - z) ≤ R}
  have hK : IsCompact K := isCompact_physical_euclidean_closedBall z R
  have hz x (hx : x ∉ K) : φ x = 0 := hzero x (not_le.mp hx).le
  have hsupport : tsupport φ ⊆ K :=
    closure_minimal (fun x hx => by by_contra hn; exact hx (hz x hn)) hK.isClosed
  have hdz j x (hx : x ∉ K) : coordinateDerivative j φ x = 0 := by
    have hxs : x ∉ tsupport φ := fun hm => hx (hsupport hm)
    simp only [coordinateDerivative, fderiv_of_notMem_tsupport ℝ hxs, zero_apply]
  have hd j : Continuous (coordinateDerivative j φ) :=
    ((contDiff_infty_iff_fderiv.mp hφ.1).2.clm_apply contDiff_const).continuous
  let χ : Vec d → ℝ := fun x =>
    (φ x ^ 2 / (4 * ε) + 4 * (∑ j, (coordinateDerivative j φ x) ^ 2)) *
      ((d : ℝ) ^ 2 * L ^ 2 / 4) + ‖ζ‖ ^ 2 * φ x ^ 2 * ((d : ℝ) * L ^ 2)
  let A := (1 / (4 * ε) + 4 * ((d : ℝ) * B ^ 2 / (R - r) ^ 2)) *
    ((d : ℝ) ^ 2 * L ^ 2 / 4) + ‖ζ‖ ^ 2 * ((d : ℝ) * L ^ 2)
  have hχ : Continuous χ :=
    (((hφ.1.continuous.pow 2).div_const _).add
      (continuous_const.mul (continuous_finsetSum _ (fun j _ => (hd j).pow 2)))).mul
        continuous_const |>.add ((continuous_const.mul (hφ.1.continuous.pow 2)).mul continuous_const)
  have hχzero x (hx : x ∉ K) : χ x = 0 := by simp [χ, hz x hx, hdz, hx]
  have hχbound x : χ x ≤ A := by
    have hs : φ x ^ 2 ≤ 1 := by nlinarith [hφrange x]
    have hder := physical_gap_cutoff_error_bound (ζ := (0 : ℂ)) hφrange hφD x
    simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), zero_mul, zero_add] at hder
    have hp := div_le_div_of_nonneg_right hs (show 0 ≤ 4 * ε by positivity)
    have hg := mul_le_mul_of_nonneg_left hder (show (0 : ℝ) ≤ 4 by norm_num)
    have hfirst := mul_le_mul_of_nonneg_right (add_le_add hp hg)
      (show 0 ≤ (d : ℝ) ^ 2 * L ^ 2 / 4 by positivity)
    have hlast := mul_le_mul_of_nonneg_left hs
      (show 0 ≤ ‖ζ‖ ^ 2 * ((d : ℝ) * L ^ 2) by positivity)
    dsimp [χ, A]
    nlinarith only [hfirst, hlast]
  have hlocalV := ae_locally_memLp_joint_spatial_translate
    (reducedLaw Q) (reducedLaw_stationary Q) hV
    (integrable_sq_joint_l2_representative
      ((((hP.2.2.1 g).comp (continuous_real_toNNReal.comp
        (continuous_id.sub continuous_const))).norm.pow 2).continuousOn.integrableOn_compact
          (μ := (volume : Measure ℝ)) (K := Icc b c) isCompact_Icc) hV heV)
  have hlocalD j : ∀ᵐ ω ∂reducedLaw Q, ∀ S : Set (Vec d), IsCompact S →
      MemLp (fun p : Vec d × ℝ => D j (p.2, translate p.1 ω)) 2
        ((volume.restrict S).prod (volume.restrict (Icc b c))) := by
    have hc : ContinuousOn (fun s : ℝ => (hP.gradientOrbit (centeredComplexLp Q f) s) j)
        (Ioi 0) :=
      (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) j).continuous.comp_continuousOn
        (hP.continuousOn_gradientOrbit (centeredComplexLp Q f))
    have hi := ((hc.norm.pow 2).mono
      (fun s (hs : s ∈ Icc b c) => lt_of_lt_of_le (ha.trans hb) hs.1)).integrableOn_compact
        (μ := (volume : Measure ℝ)) isCompact_Icc
    exact ae_locally_memLp_joint_spatial_translate (reducedLaw Q) (reducedLaw_stationary Q)
      (hD j) (integrable_sq_joint_l2_representative hi (hD j) (heD j))
  have hlocalE j : ∀ᵐ ω ∂reducedLaw Q, ∀ S : Set (Vec d), IsCompact S →
      MemLp (fun p : Vec d × ℝ => E j (p.2, translate p.1 ω)) 2
        ((volume.restrict S).prod (volume.restrict (Icc b c))) := by
    have hc : ContinuousOn (fun s : ℝ => (hP.gradientOrbit g (s - a)) j) (Ioi a) :=
      (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) j).continuous.comp_continuousOn
        ((hP.continuousOn_gradientOrbit g).comp
          (continuous_id.sub continuous_const).continuousOn (fun s hs => by
            change 0 < s - a
            exact sub_pos.mpr hs))
    have hi := ((hc.norm.pow 2).mono
      (fun s (hs : s ∈ Icc b c) => hb.trans_le hs.1)).integrableOn_compact (μ := (volume : Measure ℝ)) isCompact_Icc
    exact ae_locally_memLp_joint_spatial_translate (reducedLaw Q) (reducedLaw_stationary Q)
      (hE j) (integrable_sq_joint_l2_representative hi (hE j) (heE j))
  filter_upwards [hyoung b c hb hbc φ hφ ε hε (fun _ => 1) continuousOn_const
    (fun _ _ => zero_le_one), hlocalV, ae_all_iff.mpr hlocalD, ae_all_iff.mpr hlocalE]
    with ω hy hv hld hle
  have hiV := (memLp_two_iff_integrable_sq_norm (hv K hK).aestronglyMeasurable).mp (hv K hK)
  have hiD := integrable_finsetSum Finset.univ (fun j _ =>
    (memLp_two_iff_integrable_sq_norm (hld j K hK).aestronglyMeasurable).mp (hld j K hK))
  have hiE := integrable_finsetSum Finset.univ (fun j _ =>
    (memLp_two_iff_integrable_sq_norm (hle j K hK).aestronglyMeasurable).mp (hle j K hK))
  have hinner := physical_inner_spacetime_integral_le hK
    (isCompact_physical_euclidean_closedBall z r).measurableSet
    (fun x hx => hx.trans hrR.le) measurableSet_Icc (Subset.refl _) hiV
    (fun p => sq_nonneg _) hφ.1.continuous hz (fun x hx => hone x hx)
    (η := fun _ => 1) continuousOn_const (fun _ _ => zero_le_one) (fun _ _ => le_refl 1)
  have houterE := physical_spacetime_weight_integral_le hK hiE
    (fun p => Finset.sum_nonneg (fun j _ => sq_nonneg _)) (hφ.1.continuous.pow 2)
    (fun x hx => by simp only [Pi.pow_apply, hz x hx, zero_pow (by decide : 2 ≠ 0)])
    (η := fun _ => 1) continuousOn_const (A := 1) (by
      intro s hs x hx
      simp only [one_mul, Pi.pow_apply]
      nlinarith [hφrange x])
  have houterD := physical_spacetime_weight_integral_le hK hiD
    (fun p => Finset.sum_nonneg (fun j _ => sq_nonneg _)) hχ hχzero
    (η := fun _ => 1) continuousOn_const (A := A) (fun s hs x hx => by
      simpa only [one_mul] using hχbound x)
  simp only [one_mul, Pi.pow_apply] at hy hinner houterE houterD
  have hεouter := mul_le_mul_of_nonneg_left houterE hε.le
  change _ ≤ 2 * ε * _ + 2 * A * _
  nlinarith only [hy, hinner, hεouter, houterD]

/-- The actual derivative mass on an inner cylinder is bounded by an
one thirty-second of its outer mass and an explicit multiple of the
original corrected-orbit mass. All three physical estimates use the same
representatives; no local energy estimate is assumed. -/
theorem local_time_corrected_orbit_derivative_mass_one_step
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t a b : ℝ}
    (ht : 0 < t) (ha : 0 < a) (hab : a < b) :
    let L := Real.exp (2 * Λ₀) * Λ₀
    let K := fun (B T Δt Δx : ℝ) =>
      4 * L * (T / Δt / 2 + (2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3) *
        (‖ζ‖ ^ 2 + (d : ℝ) * B ^ 2 / Δx ^ 2))
    let A := fun (B Δx ε : ℝ) =>
      (1 / (4 * ε) + 4 * ((d : ℝ) * B ^ 2 / Δx ^ 2)) *
        ((d : ℝ) ^ 2 * L ^ 2 / 4) + ‖ζ‖ ^ 2 * ((d : ℝ) * L ^ 2)
    let w := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
    ∃ B₀ B₁ B₂ T₁ T₂ : ℝ,
      0 < B₀ ∧ 0 < B₁ ∧ 0 < B₂ ∧ 0 < T₁ ∧ 0 < T₂ ∧
      ∃ g : Lp ℂ 2 (reducedLaw Q), ∃ W V : ℝ × FieldPair d → ℂ,
      Measurable W ∧ Measurable V ∧
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] w s) ∧
      (∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] P (s - a).toNNReal g) ∧
      (∀ s, a < s → HasDerivAt w (P (s - a).toNNReal g) s ∧
        IsComplexGeneratorPair Q i ζ (w s) (P (s - a).toNNReal g)) ∧
      ∀ c e v : ℝ, b < c → c < e → e ≤ v → ∀ z : Vec d, ∀ r R S : ℝ,
        0 < r → r < R → R < S → ∀ᵐ ω ∂reducedLaw Q,
          (∫ s in Icc e v, ∫ x in {x | euclideanNorm (x - z) ≤ r},
            ‖V (s, translate x ω)‖ ^ 2) ≤
          (1 / 32 : ℝ) *
            (∫ s in Icc c v, ∫ x in {x | euclideanNorm (x - z) ≤ S},
              ‖V (s, translate x ω)‖ ^ 2) +
          2 * A B₀ (R - r) (1 / (64 * K B₁ T₁ (e - c) (S - R))) * K B₂ T₂ (e - c) (S - R) *
            (∫ s in Icc c v, ∫ x in {x | euclideanNorm (x - z) ≤ S},
              ‖W (s, translate x ω)‖ ^ 2) := by
  intro L K A w
  obtain ⟨B₀, hB₀, g, W, V, D, E, hW, hV, hD, hE, heW, heV, heD, heE,
    hregular, hout⟩ := local_time_corrected_orbit_outputMassInterpolation hP f ht ha
  obtain ⟨B₁, T₁, hB₁, hT₁, hderiv⟩ :=
    local_time_restarted_derivative_gapCaccioppoli hP f g ht ha hab V E hV hE heV heE
      (fun s hs => (hregular s hs).1)
  obtain ⟨B₂, T₂, hB₂, hT₂, horig⟩ :=
    local_time_corrected_orbit_gapCaccioppoli hP f ht ha W D hW hD heW heD
  refine ⟨B₀, B₁, B₂, T₁, T₂, hB₀, hB₁, hB₂, hT₁, hT₂,
    g, W, V, hW, hV, heW, heV, hregular, ?_⟩
  intro c e v hc hce hev z r R S hr hrR hRS
  have hL : 0 < L := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hdt : 0 < e - c := sub_pos.mpr hce
  have hK₁ : 0 < K B₁ T₁ (e - c) (S - R) := by dsimp [K]; positivity
  let ε := 1 / (64 * K B₁ T₁ (e - c) (S - R))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hcoef : 2 * ε * K B₁ T₁ (e - c) (S - R) = (1 / 32 : ℝ) := by
    dsimp [ε]
    field_simp
    ring
  have hae : a < e := hab.trans (hc.trans hce)
  filter_upwards [hout e v hae hev z r R hr hrR ε hε,
    hderiv c e v hc hce hev z R S (hr.trans hrR) hRS,
    horig c e v (hab.trans hc) hce hev z R S (hr.trans hrR) hRS]
    with ω hout hderiv horig
  have hεderiv := mul_le_mul_of_nonneg_left hderiv (show 0 ≤ 2 * ε by positivity)
  have hA : 0 ≤ 2 * A B₀ (R - r) ε := by dsimp [A]; positivity
  have hAorig := mul_le_mul_of_nonneg_left horig hA
  change _ ≤ (1 / 32 : ℝ) * _ +
    2 * A B₀ (R - r) ε * K B₂ T₂ (e - c) (S - R) * _
  change _ ≤ 2 * ε * (K B₁ T₁ (e - c) (S - R) * _) at hεderiv
  rw [← mul_assoc, hcoef] at hεderiv
  change _ ≤ 2 * A B₀ (R - r) ε * (K B₂ T₂ (e - c) (S - R) * _) at hAorig
  change _ ≤ 2 * ε * _ + 2 * A B₀ (R - r) ε * _ at hout
  nlinarith only [hout, hεderiv, hAorig]

/-- Numerical absorption for nested derivative cylinders. The fourth-order
cutoff cost grows by sixteen at each halving of the cylinder gap; choosing
contraction one thirty-second makes the accumulated error summable. -/
theorem local_time_cylinder_mass_absorption
    (F : ℕ → ℝ) {K M : ℝ} (hK : 0 ≤ K)
    (hbounded : ∀ n, F n ≤ M)
    (hstep : ∀ n, F n ≤ (1 / 32 : ℝ) * F (n + 1) + K * 16 ^ n) :
    F 0 ≤ 2 * K := by
  have hiter (n : ℕ) : F 0 ≤ (1 / 32 : ℝ) ^ n * F n +
      2 * K * (1 - (1 / 2 : ℝ) ^ n) := by
    induction n with
    | zero => simp only [pow_zero, one_mul, sub_self, mul_zero, add_zero, le_refl]
    | succ n ih =>
      have hscale : (1 / 32 : ℝ) ^ n * (K * 16 ^ n) = K * (1 / 2 : ℝ) ^ n := by
        calc
          _ = K * ((1 / 32 : ℝ) * 16) ^ n := by rw [mul_pow]; ring
          _ = _ := by norm_num
      calc
        F 0 ≤ (1 / 32 : ℝ) ^ n * F n +
            2 * K * (1 - (1 / 2 : ℝ) ^ n) := ih
        _ ≤ (1 / 32 : ℝ) ^ n *
            ((1 / 32 : ℝ) * F (n + 1) + K * 16 ^ n) +
            2 * K * (1 - (1 / 2 : ℝ) ^ n) :=
          add_le_add (mul_le_mul_of_nonneg_left (hstep n)
            (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 32) n)) (le_refl _)
        _ = _ := by rw [mul_add, hscale, pow_succ, pow_succ]; ring
  have hbound (n : ℕ) : F 0 ≤ (1 / 32 : ℝ) ^ n * M + 2 * K := by
    have htail := mul_le_mul_of_nonneg_left (hbounded n)
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 32) n)
    have herror : 0 ≤ 2 * K * (1 / 2 : ℝ) ^ n := by positivity
    nlinarith only [hiter n, htail, herror]
  have hlim : Tendsto (fun n : ℕ => (1 / 32 : ℝ) ^ n * M + 2 * K)
      atTop (nhds (2 * K)) := by
    simpa only [zero_mul, zero_add] using
      ((tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 32) (by norm_num : (1 / 32 : ℝ) < 1)).mul_const M).add_const (2 * K)
  exact ge_of_tendsto' hlim hbound

/-- Dimension-only spatial and universal temporal cutoff constants for the
actual corrected orbit; chosen before the environment and data. -/
theorem local_time_uniform_corrected_orbit_gapCaccioppoli (d : ℕ) [Fact (2 ≤ d)] :
    ∃ B T : ℝ, 0 < B ∧ 0 < T ∧
    ∀ {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t a : ℝ} (_ht : 0 < t) (_ha : 0 < a),
    let L := Real.exp (2 * Λ₀) * Λ₀
    let w := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
    ∃ g : Lp ℂ 2 (reducedLaw Q),
      ∃ W V : ℝ × FieldPair d → ℂ, ∃ D : Fin d → ℝ × FieldPair d → ℂ,
      Measurable W ∧ Measurable V ∧ (∀ j, Measurable (D j)) ∧
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] w s) ∧
      (∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] P (s - a).toNNReal g) ∧
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q]
        (hP.gradientOrbit (centeredComplexLp Q f) s) j) ∧
      (∀ r, a < r → HasDerivAt w (P (r - a).toNNReal g) r ∧
        IsComplexGeneratorPair Q i ζ (w r) (P (r - a).toNNReal g)) ∧
      ∀ b e c : ℝ, a < b → b < e → e ≤ c → ∀ z : Vec d, ∀ r R : ℝ,
        0 < r → r < R → ∀ᵐ ω ∂reducedLaw Q,
          (∫ s in Icc e c, ∫ x in {x | euclideanNorm (x - z) ≤ r},
            ∑ j, ‖D j (s, translate x ω)‖ ^ 2) ≤
          4 * L * (T / (e - b) / 2 +
            (2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3) *
              (‖ζ‖ ^ 2 + (d : ℝ) * B ^ 2 / (R - r) ^ 2)) *
            (∫ s in Icc b c, ∫ x in {x | euclideanNorm (x - z) ≤ R},
              ‖W (s, translate x ω)‖ ^ 2) := by
  obtain ⟨B, hB, hcutoff⟩ := exists_physical_gap_euclidean_cutoff d
  obtain ⟨T, hT, htime⟩ := exists_physical_gap_temporal_cutoff
  refine ⟨B, T, hB, hT, ?_⟩
  intro Λ₀ r₀ Q i ζ P hP f t a ht ha L w
  let := reducedLaw_probability Q
  obtain ⟨g, W, V, D, hW, hV, hD, heW, heV, heD, hregular, henergy⟩ :=
    complexForced_correctedOrbit_ae_physical_boundaryCutoffEnergy hP f ht ha
  refine ⟨g, W, V, D, hW, hV, hD, heW, heV, heD, hregular, ?_⟩
  have hu : Continuous (fun r : ℝ =>
      centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f))) := by
    simpa only [Function.comp_def, centeredComplexLpCLM_apply] using
      (centeredComplexLpCLM Q).continuous.comp
        ((hP.2.2.1 (centeredComplexLp Q f)).comp continuous_real_toNNReal)
  have hw : Continuous w := hu.add ((Lp.constL 2 (reducedLaw Q) ℂ).continuous.comp
    (Blueprint.continuous_centered_source_primitive hP f (t / 4)))
  have hL : 0 < L := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hC : 0 ≤ 2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3 := by positivity
  intro b e c hb hbe hec z r R hr hrR
  have hbc : b < c := hbe.trans_le hec
  obtain ⟨φ, hφ, hφrange, hone, hzero, hφD⟩ := hcutoff z r R hr hrR
  obtain ⟨η, hη, hηb, hηone, hηbounds⟩ := htime b e hbe
  have hηcont : ContinuousOn η (Icc b c) := hη.continuous.continuousOn
  have hηd : ContinuousOn (deriv η) (Icc b c) :=
    (hη.continuous_deriv (by simp)).continuousOn
  have hηac : AbsolutelyContinuousOnInterval η b c :=
    (hη.of_le (by simp)).contDiffOn.absolutelyContinuousOnInterval
  have hwI : IntegrableOn (fun s => ‖w s‖ ^ 2) (Icc b c) volume :=
    (hw.norm.pow 2).continuousOn.integrableOn_compact (μ := (volume : Measure ℝ)) isCompact_Icc
  have hlocalW := ae_locally_memLp_joint_spatial_translate
    (reducedLaw Q) (reducedLaw_stationary Q) hW
    (integrable_sq_joint_l2_representative hwI hW heW)
  have hlocalD (j : Fin d) : ∀ᵐ ω ∂reducedLaw Q,
      ∀ K : Set (Vec d), IsCompact K →
        MemLp (fun p : Vec d × ℝ => D j (p.2, translate p.1 ω)) 2
          ((volume.restrict K).prod (volume.restrict (Icc b c))) := by
    have hc : ContinuousOn (fun s : ℝ => (hP.gradientOrbit (centeredComplexLp Q f) s) j)
        (Ioi 0) :=
      (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) j).continuous.comp_continuousOn
        (hP.continuousOn_gradientOrbit (centeredComplexLp Q f))
    have hi : IntegrableOn (fun s : ℝ => ‖(hP.gradientOrbit (centeredComplexLp Q f) s) j‖ ^ 2)
        (Icc b c) volume :=
      ((hc.norm.pow 2).mono (fun _ hs => lt_of_lt_of_le (ha.trans hb) hs.1)).integrableOn_compact
        (μ := (volume : Measure ℝ)) isCompact_Icc
    exact ae_locally_memLp_joint_spatial_translate (reducedLaw Q) (reducedLaw_stationary Q)
      (hD j) (integrable_sq_joint_l2_representative hi (hD j) (heD j))
  filter_upwards [henergy b c hb hbc.le φ hφ η hηac hηd
    (fun s _ => (hηbounds s).1), hlocalW, ae_all_iff.mpr hlocalD]
    with ω hω hlW hlD
  have hK := isCompact_physical_euclidean_closedBall z R
  apply physical_spacetime_caccioppoli_of_cutoff_energy hK
    (isCompact_physical_euclidean_closedBall z r).measurableSet
    (fun x hx => hx.trans hrR.le) hL hC measurableSet_Icc
    (Icc_subset_Icc_left hbe.le) (U := fun x => (w c) (translate x ω))
    (hlW _ hK) (fun j => hlD j _ hK) hφ hφrange
    (fun x hx => hone x hx) (fun x hx => hzero x (not_le.mp hx).le)
    (fun x _ => physical_gap_cutoff_error_bound hφrange hφD x)
    hηcont hηd (fun s _ => hηbounds s) (fun s hs => (hηone s hs.1).ge)
  rw [hηb, hηone c hec, zero_mul, one_mul, zero_sub] at hω
  linarith only [hω]

/-- Dimension-only spatial and universal temporal cutoff constants for the
actual restarted derivative; chosen before the environment and data. -/
theorem local_time_uniform_restarted_derivative_gapCaccioppoli (d : ℕ) [Fact (2 ≤ d)] :
    ∃ B T : ℝ, 0 < B ∧ 0 < T ∧
    ∀ {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t a b : ℝ}
    (_ht : 0 < t) (_ha : 0 < a) (_hab : a < b),
    let L := Real.exp (2 * Λ₀) * Λ₀
    let w := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
    ∃ g h : Lp ℂ 2 (reducedLaw Q), ∃ V Z : ℝ × FieldPair d → ℂ,
      ∃ D : Fin d → ℝ × FieldPair d → ℂ,
      Measurable V ∧ Measurable Z ∧ (∀ j, Measurable (D j)) ∧
      (∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] P (s - a).toNNReal g) ∧
      (∀ s, (fun ω => Z (s, ω)) =ᵐ[reducedLaw Q] P (s - b).toNNReal h) ∧
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit g (s - a)) j) ∧
      (∀ s, a < s → HasDerivAt w (P (s - a).toNNReal g) s ∧
        IsComplexGeneratorPair Q i ζ (w s) (P (s - a).toNNReal g)) ∧
      (∀ s, b < s →
        HasDerivAt (fun r : ℝ => P (r - a).toNNReal g) (P (s - b).toNNReal h) s ∧
        IsComplexGeneratorPair Q i ζ (P (s - a).toNNReal g) (P (s - b).toNNReal h) ∧
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (P (s - a).toNNReal g) (hP.gradientOrbit g (s - a))) ∧
      (∀ᵐ ω ∂reducedLaw Q, ∀ n : ℕ, ∀ K : Set (Vec d), IsCompact K →
        MemLp (fun p : Vec d × ℝ => V (p.2, translate p.1 ω)) 2
          ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ)))) ∧
        MemLp (fun p : Vec d × ℝ => Z (p.2, translate p.1 ω)) 2
          ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ)))) ∧
        Integrable (fun p : Vec d × ℝ =>
          star (V (p.2, translate p.1 ω)) * Z (p.2, translate p.1 ω))
          ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ))))) ∧
      ∀ c e v : ℝ, b < c → c < e → e ≤ v → ∀ z : Vec d, ∀ r R : ℝ,
        0 < r → r < R → ∀ᵐ ω ∂reducedLaw Q,
          (∫ s in Icc e v, ∫ x in {x | euclideanNorm (x - z) ≤ r},
            ∑ j, ‖D j (s, translate x ω)‖ ^ 2) ≤
          4 * L * (T / (e - c) / 2 +
            (2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3) *
              (‖ζ‖ ^ 2 + (d : ℝ) * B ^ 2 / (R - r) ^ 2)) *
            (∫ s in Icc c v, ∫ x in {x | euclideanNorm (x - z) ≤ R},
              ‖V (s, translate x ω)‖ ^ 2) := by
  obtain ⟨B, hB, hcutoff⟩ := exists_physical_gap_euclidean_cutoff d
  obtain ⟨T, hT, htime⟩ := exists_physical_gap_temporal_cutoff
  refine ⟨B, T, hB, hT, ?_⟩
  intro Λ₀ r₀ Q i ζ P hP f t a b ht ha hab L w
  let := reducedLaw_probability Q
  obtain ⟨g, h, V, Z, D, hV, hZ, hD, heV, heZ, heD, hw, hd, hlocal, henergy⟩ :=
    complexForced_correctedOrbit_derivative_ae_boundaryCutoffEnergy hP f ht ha hab
  refine ⟨g, h, V, Z, D, hV, hZ, hD, heV, heZ, heD,
    hw, hd, hlocal, ?_⟩
  let u : ℝ → Lp ℂ 2 (reducedLaw Q) := fun s => P (s - a).toNNReal g
  have hu : Continuous u :=
    (hP.2.2.1 g).comp (continuous_real_toNNReal.comp (continuous_id.sub continuous_const))
  have hL : 0 < L := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hC : 0 ≤ 2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3 := by positivity
  intro c e v hc hce hev z r R hr hrR
  have hcv : c < v := hce.trans_le hev
  obtain ⟨φ, hφ, hφrange, hone, hzero, hφD⟩ := hcutoff z r R hr hrR
  obtain ⟨η, hη, hηb, hηone, hηbounds⟩ := htime c e hce
  have hηcont : ContinuousOn η (Icc c v) := hη.continuous.continuousOn
  have hηd : ContinuousOn (deriv η) (Icc c v) :=
    (hη.continuous_deriv (by simp)).continuousOn
  have hηac : AbsolutelyContinuousOnInterval η c v :=
    (hη.of_le (by simp)).contDiffOn.absolutelyContinuousOnInterval
  have hwI : IntegrableOn (fun s => ‖u s‖ ^ 2) (Icc c v) volume :=
    (hu.norm.pow 2).continuousOn.integrableOn_compact (μ := (volume : Measure ℝ)) isCompact_Icc
  have hlocalW := ae_locally_memLp_joint_spatial_translate
    (reducedLaw Q) (reducedLaw_stationary Q) hV
    (integrable_sq_joint_l2_representative hwI hV heV)
  have hlocalD (j : Fin d) : ∀ᵐ ω ∂reducedLaw Q,
      ∀ K : Set (Vec d), IsCompact K →
        MemLp (fun p : Vec d × ℝ => D j (p.2, translate p.1 ω)) 2
          ((volume.restrict K).prod (volume.restrict (Icc c v))) := by
    have hg : ContinuousOn (fun s : ℝ => hP.gradientOrbit g (s - a)) (Ioi a) :=
      (hP.continuousOn_gradientOrbit g).comp
        (continuous_id.sub continuous_const).continuousOn (fun s hs => by
          change 0 < s - a
          exact sub_pos.mpr hs)
    have hcoord : ContinuousOn (fun s : ℝ => (hP.gradientOrbit g (s - a)) j) (Ioi a) :=
      (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) j).continuous.comp_continuousOn hg
    have hi : IntegrableOn (fun s : ℝ => ‖(hP.gradientOrbit g (s - a)) j‖ ^ 2)
        (Icc c v) volume :=
      ((hcoord.norm.pow 2).mono (fun _ hs => lt_of_lt_of_le (hab.trans hc) hs.1)).integrableOn_compact
        (μ := (volume : Measure ℝ)) isCompact_Icc
    exact ae_locally_memLp_joint_spatial_translate (reducedLaw Q) (reducedLaw_stationary Q)
      (hD j) (integrable_sq_joint_l2_representative hi (hD j) (heD j))
  filter_upwards [henergy c v hc hcv.le φ hφ η hηac hηd
    (fun s _ => (hηbounds s).1), hlocalW, ae_all_iff.mpr hlocalD]
    with ω hω hlW hlD
  have hK := isCompact_physical_euclidean_closedBall z R
  apply physical_spacetime_caccioppoli_of_cutoff_energy hK
    (isCompact_physical_euclidean_closedBall z r).measurableSet
    (fun x hx => hx.trans hrR.le) hL hC measurableSet_Icc
    (Icc_subset_Icc_left hce.le) (U := fun x => (u v) (translate x ω))
    (hlW _ hK) (fun j => hlD j _ hK) hφ hφrange
    (fun x hx => hone x hx) (fun x hx => hzero x (not_le.mp hx).le)
    (fun x _ => physical_gap_cutoff_error_bound hφrange hφD x)
    hηcont hηd (fun s _ => hηbounds s) (fun s hs => (hηone s hs.1).ge)
  rw [hηb, hηone v hev, zero_mul, one_mul, zero_sub] at hω
  linarith only [hω]

/-- Output Young interpolation with a dimension-only cutoff constant. -/
theorem local_time_uniform_corrected_orbit_outputMassInterpolation
    (d : ℕ) [Fact (2 ≤ d)] :
    ∃ B : ℝ, 0 < B ∧
    ∀ {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t a : ℝ} (_ht : 0 < t) (_ha : 0 < a),
    let L := Real.exp (2 * Λ₀) * Λ₀
    let w := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
    ∃ g : Lp ℂ 2 (reducedLaw Q),
      ∃ W V : ℝ × FieldPair d → ℂ, ∃ D E : Fin d → ℝ × FieldPair d → ℂ,
      Measurable W ∧ Measurable V ∧ (∀ j, Measurable (D j)) ∧ (∀ j, Measurable (E j)) ∧
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] w s) ∧
      (∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] P (s - a).toNNReal g) ∧
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q]
        (hP.gradientOrbit (centeredComplexLp Q f) s) j) ∧
      (∀ j s, (fun ω => E j (s, ω)) =ᵐ[reducedLaw Q]
        (hP.gradientOrbit g (s - a)) j) ∧
      (∀ r, a < r → HasDerivAt w (P (r - a).toNNReal g) r ∧
        IsComplexGeneratorPair Q i ζ (w r) (P (r - a).toNNReal g)) ∧
      ∀ b c : ℝ, a < b → b ≤ c → ∀ z : Vec d, ∀ r R : ℝ,
        0 < r → r < R → ∀ ε : ℝ, 0 < ε → ∀ᵐ ω ∂reducedLaw Q,
          (∫ s in Icc b c, ∫ x in {x | euclideanNorm (x - z) ≤ r},
            ‖V (s, translate x ω)‖ ^ 2) ≤
          2 * ε * (∫ s in Icc b c, ∫ x in {x | euclideanNorm (x - z) ≤ R},
            ∑ j, ‖E j (s, translate x ω)‖ ^ 2) +
          2 * ((1 / (4 * ε) + 4 * ((d : ℝ) * B ^ 2 / (R - r) ^ 2)) *
            ((d : ℝ) ^ 2 * L ^ 2 / 4) + ‖ζ‖ ^ 2 * ((d : ℝ) * L ^ 2)) *
            (∫ s in Icc b c, ∫ x in {x | euclideanNorm (x - z) ≤ R},
              ∑ j, ‖D j (s, translate x ω)‖ ^ 2) := by
  obtain ⟨B, hB, hcutoff⟩ := exists_physical_gap_euclidean_cutoff d
  refine ⟨B, hB, ?_⟩
  intro Λ₀ r₀ Q i ζ P hP f t a ht ha L w
  let := reducedLaw_probability Q
  obtain ⟨g, W, V, D, E, hW, hV, hD, hE, heW, heV, heD, heE, hregular, hyoung⟩ :=
    complexForced_correctedOrbit_ae_physical_integratedOutputYoung hP f ht ha
  refine ⟨g, W, V, D, E, hW, hV, hD, hE, heW, heV, heD, heE, hregular, ?_⟩
  intro b c hb hbc z r R hr hrR ε hε
  obtain ⟨φ, hφ, hφrange, hone, hzero, hφD⟩ := hcutoff z r R hr hrR
  let K := {x : Vec d | euclideanNorm (x - z) ≤ R}
  have hK : IsCompact K := isCompact_physical_euclidean_closedBall z R
  have hz x (hx : x ∉ K) : φ x = 0 := hzero x (not_le.mp hx).le
  have hsupport : tsupport φ ⊆ K :=
    closure_minimal (fun x hx => by by_contra hn; exact hx (hz x hn)) hK.isClosed
  have hdz j x (hx : x ∉ K) : coordinateDerivative j φ x = 0 := by
    have hxs : x ∉ tsupport φ := fun hm => hx (hsupport hm)
    simp only [coordinateDerivative, fderiv_of_notMem_tsupport ℝ hxs, zero_apply]
  have hd j : Continuous (coordinateDerivative j φ) :=
    ((contDiff_infty_iff_fderiv.mp hφ.1).2.clm_apply contDiff_const).continuous
  let χ : Vec d → ℝ := fun x =>
    (φ x ^ 2 / (4 * ε) + 4 * (∑ j, (coordinateDerivative j φ x) ^ 2)) *
      ((d : ℝ) ^ 2 * L ^ 2 / 4) + ‖ζ‖ ^ 2 * φ x ^ 2 * ((d : ℝ) * L ^ 2)
  let A := (1 / (4 * ε) + 4 * ((d : ℝ) * B ^ 2 / (R - r) ^ 2)) *
    ((d : ℝ) ^ 2 * L ^ 2 / 4) + ‖ζ‖ ^ 2 * ((d : ℝ) * L ^ 2)
  have hχ : Continuous χ :=
    (((hφ.1.continuous.pow 2).div_const _).add
      (continuous_const.mul (continuous_finsetSum _ (fun j _ => (hd j).pow 2)))).mul
        continuous_const |>.add ((continuous_const.mul (hφ.1.continuous.pow 2)).mul continuous_const)
  have hχzero x (hx : x ∉ K) : χ x = 0 := by simp [χ, hz x hx, hdz, hx]
  have hχbound x : χ x ≤ A := by
    have hs : φ x ^ 2 ≤ 1 := by nlinarith [hφrange x]
    have hder := physical_gap_cutoff_error_bound (ζ := (0 : ℂ)) hφrange hφD x
    simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), zero_mul, zero_add] at hder
    have hp := div_le_div_of_nonneg_right hs (show 0 ≤ 4 * ε by positivity)
    have hg := mul_le_mul_of_nonneg_left hder (show (0 : ℝ) ≤ 4 by norm_num)
    have hfirst := mul_le_mul_of_nonneg_right (add_le_add hp hg)
      (show 0 ≤ (d : ℝ) ^ 2 * L ^ 2 / 4 by positivity)
    have hlast := mul_le_mul_of_nonneg_left hs
      (show 0 ≤ ‖ζ‖ ^ 2 * ((d : ℝ) * L ^ 2) by positivity)
    dsimp [χ, A]
    nlinarith only [hfirst, hlast]
  have hlocalV := ae_locally_memLp_joint_spatial_translate
    (reducedLaw Q) (reducedLaw_stationary Q) hV
    (integrable_sq_joint_l2_representative
      ((((hP.2.2.1 g).comp (continuous_real_toNNReal.comp
        (continuous_id.sub continuous_const))).norm.pow 2).continuousOn.integrableOn_compact
          (μ := (volume : Measure ℝ)) (K := Icc b c) isCompact_Icc) hV heV)
  have hlocalD j : ∀ᵐ ω ∂reducedLaw Q, ∀ S : Set (Vec d), IsCompact S →
      MemLp (fun p : Vec d × ℝ => D j (p.2, translate p.1 ω)) 2
        ((volume.restrict S).prod (volume.restrict (Icc b c))) := by
    have hc : ContinuousOn (fun s : ℝ => (hP.gradientOrbit (centeredComplexLp Q f) s) j)
        (Ioi 0) :=
      (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) j).continuous.comp_continuousOn
        (hP.continuousOn_gradientOrbit (centeredComplexLp Q f))
    have hi := ((hc.norm.pow 2).mono
      (fun s (hs : s ∈ Icc b c) => lt_of_lt_of_le (ha.trans hb) hs.1)).integrableOn_compact
        (μ := (volume : Measure ℝ)) isCompact_Icc
    exact ae_locally_memLp_joint_spatial_translate (reducedLaw Q) (reducedLaw_stationary Q)
      (hD j) (integrable_sq_joint_l2_representative hi (hD j) (heD j))
  have hlocalE j : ∀ᵐ ω ∂reducedLaw Q, ∀ S : Set (Vec d), IsCompact S →
      MemLp (fun p : Vec d × ℝ => E j (p.2, translate p.1 ω)) 2
        ((volume.restrict S).prod (volume.restrict (Icc b c))) := by
    have hc : ContinuousOn (fun s : ℝ => (hP.gradientOrbit g (s - a)) j) (Ioi a) :=
      (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) j).continuous.comp_continuousOn
        ((hP.continuousOn_gradientOrbit g).comp
          (continuous_id.sub continuous_const).continuousOn (fun s hs => by
            change 0 < s - a
            exact sub_pos.mpr hs))
    have hi := ((hc.norm.pow 2).mono
      (fun s (hs : s ∈ Icc b c) => hb.trans_le hs.1)).integrableOn_compact (μ := (volume : Measure ℝ)) isCompact_Icc
    exact ae_locally_memLp_joint_spatial_translate (reducedLaw Q) (reducedLaw_stationary Q)
      (hE j) (integrable_sq_joint_l2_representative hi (hE j) (heE j))
  filter_upwards [hyoung b c hb hbc φ hφ ε hε (fun _ => 1) continuousOn_const
    (fun _ _ => zero_le_one), hlocalV, ae_all_iff.mpr hlocalD, ae_all_iff.mpr hlocalE]
    with ω hy hv hld hle
  have hiV := (memLp_two_iff_integrable_sq_norm (hv K hK).aestronglyMeasurable).mp (hv K hK)
  have hiD := integrable_finsetSum Finset.univ (fun j _ =>
    (memLp_two_iff_integrable_sq_norm (hld j K hK).aestronglyMeasurable).mp (hld j K hK))
  have hiE := integrable_finsetSum Finset.univ (fun j _ =>
    (memLp_two_iff_integrable_sq_norm (hle j K hK).aestronglyMeasurable).mp (hle j K hK))
  have hinner := physical_inner_spacetime_integral_le hK
    (isCompact_physical_euclidean_closedBall z r).measurableSet
    (fun x hx => hx.trans hrR.le) measurableSet_Icc (Subset.refl _) hiV
    (fun p => sq_nonneg _) hφ.1.continuous hz (fun x hx => hone x hx)
    (η := fun _ => 1) continuousOn_const (fun _ _ => zero_le_one) (fun _ _ => le_refl 1)
  have houterE := physical_spacetime_weight_integral_le hK hiE
    (fun p => Finset.sum_nonneg (fun j _ => sq_nonneg _)) (hφ.1.continuous.pow 2)
    (fun x hx => by simp only [Pi.pow_apply, hz x hx, zero_pow (by decide : 2 ≠ 0)])
    (η := fun _ => 1) continuousOn_const (A := 1) (by
      intro s hs x hx
      simp only [one_mul, Pi.pow_apply]
      nlinarith [hφrange x])
  have houterD := physical_spacetime_weight_integral_le hK hiD
    (fun p => Finset.sum_nonneg (fun j _ => sq_nonneg _)) hχ hχzero
    (η := fun _ => 1) continuousOn_const (A := A) (fun s hs x hx => by
      simpa only [one_mul] using hχbound x)
  simp only [one_mul, Pi.pow_apply] at hy hinner houterE houterD
  have hεouter := mul_le_mul_of_nonneg_left houterE hε.le
  change _ ≤ 2 * ε * _ + 2 * A * _
  nlinarith only [hy, hinner, hεouter, houterD]

/-- Uniform actual-orbit mass contraction. All five cutoff constants depend
only on dimension; ellipticity and force dependence stay explicit. -/
theorem local_time_uniform_corrected_orbit_derivative_mass_one_step
    (d : ℕ) [Fact (2 ≤ d)] :
    ∃ B₀ B₁ B₂ T₁ T₂ : ℝ,
      0 < B₀ ∧ 0 < B₁ ∧ 0 < B₂ ∧ 0 < T₁ ∧ 0 < T₂ ∧
    ∀ {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t a b : ℝ}
    (_ht : 0 < t) (_ha : 0 < a) (_hab : a < b),
    let L := Real.exp (2 * Λ₀) * Λ₀
    let K := fun (B T Δt Δx : ℝ) =>
      4 * L * (T / Δt / 2 + (2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3) *
        (‖ζ‖ ^ 2 + (d : ℝ) * B ^ 2 / Δx ^ 2))
    let A := fun (B Δx ε : ℝ) =>
      (1 / (4 * ε) + 4 * ((d : ℝ) * B ^ 2 / Δx ^ 2)) *
        ((d : ℝ) ^ 2 * L ^ 2 / 4) + ‖ζ‖ ^ 2 * ((d : ℝ) * L ^ 2)
    let w := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
    ∃ g : Lp ℂ 2 (reducedLaw Q), ∃ W V : ℝ × FieldPair d → ℂ,
      Measurable W ∧ Measurable V ∧
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] w s) ∧
      (∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] P (s - a).toNNReal g) ∧
      (∀ s, a < s → HasDerivAt w (P (s - a).toNNReal g) s ∧
        IsComplexGeneratorPair Q i ζ (w s) (P (s - a).toNNReal g)) ∧
      ∀ c e v : ℝ, b < c → c < e → e ≤ v → ∀ z : Vec d, ∀ r R S : ℝ,
        0 < r → r < R → R < S → ∀ᵐ ω ∂reducedLaw Q,
          (∫ s in Icc e v, ∫ x in {x | euclideanNorm (x - z) ≤ r},
            ‖V (s, translate x ω)‖ ^ 2) ≤
          (1 / 32 : ℝ) *
            (∫ s in Icc c v, ∫ x in {x | euclideanNorm (x - z) ≤ S},
              ‖V (s, translate x ω)‖ ^ 2) +
          2 * A B₀ (R - r) (1 / (64 * K B₁ T₁ (e - c) (S - R))) * K B₂ T₂ (e - c) (S - R) *
            (∫ s in Icc c v, ∫ x in {x | euclideanNorm (x - z) ≤ S},
              ‖W (s, translate x ω)‖ ^ 2) := by
  obtain ⟨B₀, hB₀, houtput⟩ :=
    local_time_uniform_corrected_orbit_outputMassInterpolation d
  obtain ⟨B₁, T₁, hB₁, hT₁, hderivative⟩ :=
    local_time_uniform_restarted_derivative_gapCaccioppoli d
  obtain ⟨B₂, T₂, hB₂, hT₂, horiginal⟩ :=
    local_time_uniform_corrected_orbit_gapCaccioppoli d
  refine ⟨B₀, B₁, B₂, T₁, T₂, hB₀, hB₁, hB₂, hT₁, hT₂, ?_⟩
  intro Λ₀ r₀ Q i ζ P hP f t a b ht ha hab L K A w
  obtain ⟨g, W, V, D, E, hW, hV, hD, hE, heW, heV, heD, heE,
    hregular, hout⟩ := houtput hP f ht ha
  obtain ⟨g', h, V', Z, E', hV', hZ, hE', heV', heZ, heE',
    hw, hd, hlocal, hderiv⟩ := hderivative hP f ht ha hab
  have hgg : g' = g := hP.restart_derivative_unique
    (fun s hs => (hw s hs).1) (fun s hs => (hregular s hs).1)
  subst g'
  obtain ⟨g'', W', V'', D', hW', hV'', hD', heW', heV'', heD',
    hw', horig⟩ := horiginal hP f ht ha
  refine ⟨g, W, V, hW, hV, heW, heV, hregular, ?_⟩
  intro c e v hc hce hev z r R S hr hrR hRS
  have hL : 0 < L := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hdt : 0 < e - c := sub_pos.mpr hce
  have hK₁ : 0 < K B₁ T₁ (e - c) (S - R) := by dsimp [K]; positivity
  let ε := 1 / (64 * K B₁ T₁ (e - c) (S - R))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hcoef : 2 * ε * K B₁ T₁ (e - c) (S - R) = (1 / 32 : ℝ) := by
    dsimp [ε]
    field_simp
    ring
  have hae : a < e := hab.trans (hc.trans hce)
  have hderivGrad := local_time_physical_cylinder_integral_congr hE hE'
    (fun j s => (heE j s).trans (heE' j s).symm)
    (fun u => ∑ j, ‖u j‖ ^ 2) (Icc e v) {x | euclideanNorm (x - z) ≤ R}
  have hderivMass := local_time_physical_cylinder_integral_congr
    (κ := Unit) (fun _ => hV) (fun _ => hV')
    (fun _ s => (heV s).trans (heV' s).symm)
    (fun u => ‖u ()‖ ^ 2) (Icc c v) {x | euclideanNorm (x - z) ≤ S}
  have horigGrad := local_time_physical_cylinder_integral_congr hD hD'
    (fun j s => (heD j s).trans (heD' j s).symm)
    (fun u => ∑ j, ‖u j‖ ^ 2) (Icc e v) {x | euclideanNorm (x - z) ≤ R}
  have horigMass := local_time_physical_cylinder_integral_congr
    (κ := Unit) (fun _ => hW) (fun _ => hW')
    (fun _ s => (heW s).trans (heW' s).symm)
    (fun u => ‖u ()‖ ^ 2) (Icc c v) {x | euclideanNorm (x - z) ≤ S}
  filter_upwards [hout e v hae hev z r R hr hrR ε hε,
    hderiv c e v hc hce hev z R S (hr.trans hrR) hRS,
    horig c e v (hab.trans hc) hce hev z R S (hr.trans hrR) hRS,
    hderivGrad, hderivMass, horigGrad, horigMass]
    with ω hout hderiv horig hderivGrad hderivMass horigGrad horigMass
  rw [← hderivGrad, ← hderivMass] at hderiv
  rw [← horigGrad, ← horigMass] at horig
  have hεderiv := mul_le_mul_of_nonneg_left hderiv (show 0 ≤ 2 * ε by positivity)
  have hA : 0 ≤ 2 * A B₀ (R - r) ε := by dsimp [A]; positivity
  have hAorig := mul_le_mul_of_nonneg_left horig hA
  change _ ≤ (1 / 32 : ℝ) * _ +
    2 * A B₀ (R - r) ε * K B₂ T₂ (e - c) (S - R) * _
  change _ ≤ 2 * ε * (K B₁ T₁ (e - c) (S - R) * _) at hεderiv
  rw [← mul_assoc, hcoef] at hεderiv
  change _ ≤ 2 * A B₀ (R - r) ε * (K B₂ T₂ (e - c) (S - R) * _) at hAorig
  change _ ≤ 2 * ε * _ + 2 * A B₀ (R - r) ε * _ at hout
  nlinarith only [hout, hεderiv, hAorig]

/-- Monotonicity of an integrable nonnegative physical cylinder mass. -/
theorem local_time_cylinder_integral_mono {d : ℕ} {K S : Set (Vec d)}
    {I J : Set ℝ} (hSK : S ⊆ K) (hJI : J ⊆ I)
    {F : Vec d × ℝ → ℝ}
    (hF : Integrable F ((volume.restrict K).prod (volume.restrict I)))
    (hpos : ∀ p, 0 ≤ F p) :
    (∫ s in J, ∫ x in S, F (x, s)) ≤ ∫ s in I, ∫ x in K, F (x, s) := by
  have hm : (volume.restrict S).prod (volume.restrict J) ≤
      (volume.restrict K).prod (volume.restrict I) :=
    Measure.prod_mono (Measure.restrict_mono hSK le_rfl)
    (Measure.restrict_mono hJI le_rfl)
  rw [← integral_prod_symm _ (hF.mono_measure hm), ← integral_prod_symm _ hF]
  exact integral_mono_measure hm (ae_of_all _ hpos) hF

/-- Fourth-order growth of the explicit Young--Caccioppoli residual under
parabolic shrinking of the cutoff gaps. -/
theorem local_time_cutoff_residual_scale
    {L N Z B₀ B₁ B₂ T₁ T₂ δ h u : ℝ}
    (hL : 0 ≤ L) (hN : 0 ≤ N) (hZ : 0 ≤ Z)
    (hT₁ : 0 ≤ T₁) (hT₂ : 0 ≤ T₂)
    (hδ : 0 < δ) (hh : 0 < h) (hu : 1 ≤ u) :
    let K := fun (B T Δt Δx : ℝ) =>
      4 * L * (T / Δt / 2 + 2 * N * (N + 1) * L ^ 3 *
        (Z + N * B ^ 2 / Δx ^ 2))
    let A := fun (B Δx ε : ℝ) =>
      (1 / (4 * ε) + 4 * (N * B ^ 2 / Δx ^ 2)) * (N ^ 2 * L ^ 2 / 4) +
        Z * (N * L ^ 2)
    2 * A B₀ (h / u) (1 / (64 * K B₁ T₁ (δ / u ^ 2) (h / u))) *
        K B₂ T₂ (δ / u ^ 2) (h / u) ≤
      (2 * A B₀ h (1 / (64 * K B₁ T₁ δ h)) * K B₂ T₂ δ h) * u ^ 4 := by
  intro K A
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hu2 : 1 ≤ u ^ 2 := one_le_pow₀ hu
  have hforce : 0 ≤ 4 * L * (2 * N * (N + 1) * L ^ 3) * Z := by positivity
  have hK (B T : ℝ) : K B T (δ / u ^ 2) (h / u) =
      u ^ 2 * K B T δ h - (u ^ 2 - 1) *
        (4 * L * (2 * N * (N + 1) * L ^ 3) * Z) := by
    dsimp [K]
    field_simp
    ring
  have hKle (B T : ℝ) : K B T (δ / u ^ 2) (h / u) ≤ u ^ 2 * K B T δ h := by
    rw [hK]
    exact sub_le_self _ (mul_nonneg (sub_nonneg.mpr hu2) hforce)
  have hspace : N * B₀ ^ 2 / (h / u) ^ 2 = u ^ 2 * (N * B₀ ^ 2 / h ^ 2) := by
    field_simp
  have hinv (k : ℝ) : 1 / (4 * (1 / (64 * k))) = 16 * k := by
    simp only [one_div, mul_inv_rev, inv_inv]
    ring
  have hAle : A B₀ (h / u) (1 / (64 * K B₁ T₁ (δ / u ^ 2) (h / u))) ≤
      u ^ 2 * A B₀ h (1 / (64 * K B₁ T₁ δ h)) := by
    dsimp [A]
    rw [hinv, hinv, hspace]
    have hfirst := mul_le_mul_of_nonneg_right
      (add_le_add (mul_le_mul_of_nonneg_left (hKle B₁ T₁) (by norm_num : (0 : ℝ) ≤ 16))
        (le_refl (4 * (u ^ 2 * (N * B₀ ^ 2 / h ^ 2)))))
      (show 0 ≤ N ^ 2 * L ^ 2 / 4 by positivity)
    have hlast : Z * (N * L ^ 2) ≤ u ^ 2 * (Z * (N * L ^ 2)) :=
      le_mul_of_one_le_left (by positivity) hu2
    nlinarith only [hfirst, hlast]
  calc
    _ ≤ 2 * (u ^ 2 * A B₀ h (1 / (64 * K B₁ T₁ δ h))) *
        (u ^ 2 * K B₂ T₂ δ h) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hAle (by norm_num)) (hKle B₂ T₂)
        (by dsimp [K]; positivity) (by dsimp [A, K]; positivity)
    _ = _ := by ring

/-- Derivative cylinder mass controlled solely by the actual corrected-orbit
mass. Nested cylinders absorb the outer derivative term on one countable AE event. -/
theorem local_time_uniform_corrected_orbit_derivative_cylinder
    (d : ℕ) [Fact (2 ≤ d)] :
    ∃ B₀ B₁ B₂ T₁ T₂ : ℝ,
      0 < B₀ ∧ 0 < B₁ ∧ 0 < B₂ ∧ 0 < T₁ ∧ 0 < T₂ ∧
    ∀ {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t a b : ℝ}
    (_ht : 0 < t) (_ha : 0 < a) (_hab : a < b),
    let L := Real.exp (2 * Λ₀) * Λ₀
    let K := fun (B T Δt Δx : ℝ) =>
      4 * L * (T / Δt / 2 + (2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3) *
        (‖ζ‖ ^ 2 + (d : ℝ) * B ^ 2 / Δx ^ 2))
    let A := fun (B Δx ε : ℝ) =>
      (1 / (4 * ε) + 4 * ((d : ℝ) * B ^ 2 / Δx ^ 2)) *
        ((d : ℝ) ^ 2 * L ^ 2 / 4) + ‖ζ‖ ^ 2 * ((d : ℝ) * L ^ 2)
    let w := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
    ∃ g : Lp ℂ 2 (reducedLaw Q), ∃ W V : ℝ × FieldPair d → ℂ,
      Measurable W ∧ Measurable V ∧
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] w s) ∧
      (∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] P (s - a).toNNReal g) ∧
      (∀ s, a < s → HasDerivAt w (P (s - a).toNNReal g) s ∧
        IsComplexGeneratorPair Q i ζ (w s) (P (s - a).toNNReal g)) ∧
      ∀ c e v : ℝ, b < c → c < e → e ≤ v → ∀ z : Vec d, ∀ r R : ℝ,
        0 < r → r < R → ∀ᵐ ω ∂reducedLaw Q,
          (∫ s in Icc e v, ∫ x in {x | euclideanNorm (x - z) ≤ r},
            ‖V (s, translate x ω)‖ ^ 2) ≤
          4 * A B₀ ((R - r) / 4)
              (1 / (64 * K B₁ T₁ (3 * (e - c) / 4) ((R - r) / 4))) *
            K B₂ T₂ (3 * (e - c) / 4) ((R - r) / 4) *
            (∫ s in Icc c v, ∫ x in {x | euclideanNorm (x - z) ≤ R},
              ‖W (s, translate x ω)‖ ^ 2) := by
  obtain ⟨B₀, B₁, B₂, T₁, T₂, hB₀, hB₁, hB₂, hT₁, hT₂, hproducer⟩ :=
    local_time_uniform_corrected_orbit_derivative_mass_one_step d
  refine ⟨B₀, B₁, B₂, T₁, T₂, hB₀, hB₁, hB₂, hT₁, hT₂, ?_⟩
  intro Λ₀ r₀ Q i ζ P hP f t a b ht ha hab L K A w
  obtain ⟨g, W, V, hW, hV, heW, heV, hregular, hstep⟩ := hproducer hP f ht ha hab
  refine ⟨g, W, V, hW, hV, heW, heV, hregular, ?_⟩
  intro c e v hc hce hev z r R hr hrR
  let := reducedLaw_probability Q
  let τ : ℕ → ℝ := fun n => c + (e - c) / (4 : ℝ) ^ n
  let ρ : ℕ → ℝ := fun n => R - (R - r) / (2 : ℝ) ^ n
  let σ : ℕ → ℝ := fun n => (ρ n + ρ (n + 1)) / 2
  let δ := 3 * (e - c) / 4
  let h := (R - r) / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hh : 0 < h := by dsimp [h]; positivity
  have hL : 0 < L := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hpow (n : ℕ) : ((2 : ℝ) ^ n) ^ 2 = (4 : ℝ) ^ n := by
    rw [pow_two, ← mul_pow]
    norm_num
  have hτc (n : ℕ) : c < τ n := by
    dsimp [τ]
    exact lt_add_of_pos_right c (div_pos (sub_pos.mpr hce) (by positivity))
  have hτe (n : ℕ) : τ n ≤ e := by
    have hi := div_le_self (sub_nonneg.mpr hce.le)
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 4) : 1 ≤ (4 : ℝ) ^ n)
    dsimp [τ]
    linarith only [hi]
  have hτgap (n : ℕ) : τ n - τ (n + 1) = δ / ((2 : ℝ) ^ n) ^ 2 := by
    dsimp [τ, δ]
    rw [hpow n, pow_succ]
    field_simp
    ring
  have hτstep (n : ℕ) : τ (n + 1) < τ n := by
    have hp : 0 < δ / ((2 : ℝ) ^ n) ^ 2 := by positivity
    linarith only [hτgap n, hp]
  have hρr (n : ℕ) : r ≤ ρ n := by
    have hi := div_le_self (sub_nonneg.mpr hrR.le)
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) : 1 ≤ (2 : ℝ) ^ n)
    dsimp [ρ]
    linarith only [hi]
  have hρR (n : ℕ) : ρ n < R := by
    dsimp [ρ]
    exact sub_lt_self R (div_pos (sub_pos.mpr hrR) (by positivity))
  have hσleft (n : ℕ) : σ n - ρ n = h / (2 : ℝ) ^ n := by
    dsimp [σ, ρ, h]
    rw [pow_succ]
    field_simp
    ring
  have hσright (n : ℕ) : ρ (n + 1) - σ n = h / (2 : ℝ) ^ n := by
    dsimp [σ, ρ, h]
    rw [pow_succ]
    field_simp
    ring
  have hρσ (n : ℕ) : ρ n < σ n := by
    have hp : 0 < h / (2 : ℝ) ^ n := by positivity
    linarith only [hσleft n, hp]
  have hσρ (n : ℕ) : σ n < ρ (n + 1) := by
    have hp : 0 < h / (2 : ℝ) ^ n := by positivity
    linarith only [hσright n, hp]
  have huV : Continuous (fun s : ℝ => P (s - a).toNNReal g) :=
    (hP.2.2.1 g).comp (continuous_real_toNNReal.comp (continuous_id.sub continuous_const))
  have hu : Continuous (fun s : ℝ =>
      centeredComplexLp Q (P s.toNNReal (centeredComplexLp Q f))) := by
    simpa only [Function.comp_def, centeredComplexLpCLM_apply] using
      (centeredComplexLpCLM Q).continuous.comp
        ((hP.2.2.1 (centeredComplexLp Q f)).comp continuous_real_toNNReal)
  have huw : Continuous w := hu.add ((Lp.constL 2 (reducedLaw Q) ℂ).continuous.comp
    (Blueprint.continuous_centered_source_primitive hP f (t / 4)))
  have hlocalV := ae_locally_memLp_joint_spatial_translate
    (reducedLaw Q) (reducedLaw_stationary Q) hV
    (integrable_sq_joint_l2_representative
      ((huV.norm.pow 2).continuousOn.integrableOn_compact
        (μ := (volume : Measure ℝ)) (K := Icc c v) isCompact_Icc) hV heV)
  have hlocalW := ae_locally_memLp_joint_spatial_translate
    (reducedLaw Q) (reducedLaw_stationary Q) hW
    (integrable_sq_joint_l2_representative
      ((huw.norm.pow 2).continuousOn.integrableOn_compact
        (μ := (volume : Measure ℝ)) (K := Icc c v) isCompact_Icc) hW heW)
  have hall := ae_all_iff.mpr (fun n : ℕ =>
    hstep (τ (n + 1)) (τ n) v (hc.trans (hτc _)) (hτstep n)
      ((hτe n).trans hev) z (ρ n) (σ n) (ρ (n + 1))
      (hr.trans_le (hρr n)) (hρσ n) (hσρ n))
  filter_upwards [hlocalV, hlocalW, hall] with ω hlocV hlocW hrec
  let outer := {x : Vec d | euclideanNorm (x - z) ≤ R}
  have houter : IsCompact outer := isCompact_physical_euclidean_closedBall z R
  have hiV := (memLp_two_iff_integrable_sq_norm (hlocV outer houter).aestronglyMeasurable).mp
    (hlocV outer houter)
  have hiW := (memLp_two_iff_integrable_sq_norm (hlocW outer houter).aestronglyMeasurable).mp
    (hlocW outer houter)
  let F : ℕ → ℝ := fun n => ∫ s in Icc (τ n) v,
    ∫ x in {x | euclideanNorm (x - z) ≤ ρ n}, ‖V (s, translate x ω)‖ ^ 2
  let MW := ∫ s in Icc c v, ∫ x in outer, ‖W (s, translate x ω)‖ ^ 2
  let MV := ∫ s in Icc c v, ∫ x in outer, ‖V (s, translate x ω)‖ ^ 2
  let C₀ := 2 * A B₀ h (1 / (64 * K B₁ T₁ δ h)) * K B₂ T₂ δ h
  have hMW : 0 ≤ MW := integral_nonneg (fun _ => integral_nonneg (fun _ => sq_nonneg _))
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀, A, K]; positivity
  have hbounded (n : ℕ) : F n ≤ MV :=
    local_time_cylinder_integral_mono (fun _ hx => hx.trans (hρR n).le)
      (Icc_subset_Icc_left (hτc n).le) hiV (fun _ => sq_nonneg _)
  have hrecurrence (n : ℕ) : F n ≤ (1 / 32 : ℝ) * F (n + 1) +
      (C₀ * MW) * 16 ^ n := by
    have hmW : (∫ s in Icc (τ (n + 1)) v,
        ∫ x in {x | euclideanNorm (x - z) ≤ ρ (n + 1)},
          ‖W (s, translate x ω)‖ ^ 2) ≤ MW :=
      local_time_cylinder_integral_mono (fun _ hx => hx.trans (hρR _).le)
        (Icc_subset_Icc_left (hτc _).le) hiW (fun _ => sq_nonneg _)
    have hscale := local_time_cutoff_residual_scale (B₀ := B₀) (B₁ := B₁) (B₂ := B₂)
      hL.le (Nat.cast_nonneg d) (sq_nonneg ‖ζ‖) hT₁.le hT₂.le hδ hh
      (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) : 1 ≤ (2 : ℝ) ^ n)
    change 2 * A B₀ (h / (2 : ℝ) ^ n)
        (1 / (64 * K B₁ T₁ (δ / ((2 : ℝ) ^ n) ^ 2) (h / (2 : ℝ) ^ n))) *
        K B₂ T₂ (δ / ((2 : ℝ) ^ n) ^ 2) (h / (2 : ℝ) ^ n) ≤
      C₀ * ((2 : ℝ) ^ n) ^ 4 at hscale
    have hp16 : ((2 : ℝ) ^ n) ^ 4 = (16 : ℝ) ^ n := by
      rw [← pow_mul, Nat.mul_comm n 4, pow_mul]
      norm_num
    rw [hp16] at hscale
    have hn := hrec n
    rw [hτgap, hσleft, hσright] at hn
    have hcoeff : 0 ≤ 2 * A B₀ (h / (2 : ℝ) ^ n)
        (1 / (64 * K B₁ T₁ (δ / ((2 : ℝ) ^ n) ^ 2) (h / (2 : ℝ) ^ n))) *
        K B₂ T₂ (δ / ((2 : ℝ) ^ n) ^ 2) (h / (2 : ℝ) ^ n) := by
      dsimp [A, K]
      positivity
    have herror := (mul_le_mul_of_nonneg_left hmW hcoeff).trans
      (mul_le_mul_of_nonneg_right hscale hMW)
    change F n ≤ (1 / 32 : ℝ) * F (n + 1) + _ at hn
    have hfinal := hn.trans (add_le_add (le_refl _) herror)
    convert hfinal using 1
    ring
  have hresult := local_time_cylinder_mass_absorption F (mul_nonneg hC₀ hMW)
    hbounded hrecurrence
  calc
    _ = F 0 := by simp only [F, τ, ρ, pow_zero, div_one, add_sub_cancel, sub_sub_cancel]
    _ ≤ 2 * (C₀ * MW) := hresult
    _ = _ := by dsimp [C₀, δ, h, MW, outer]; ring

/-- A dimension-uniform cutoff constant for the restarted derivative time slice. -/
theorem local_time_uniform_restarted_derivative_timeSliceL2
    (d : ℕ) [Fact (2 ≤ d)] :
    ∃ B : ℝ, 0 < B ∧
    ∀ {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t a b : ℝ}
    (_ht : 0 < t) (_ha : 0 < a) (_hab : a < b),
    let L := Real.exp (2 * Λ₀) * Λ₀
    let w := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
    ∃ g h : Lp ℂ 2 (reducedLaw Q), ∃ V Z : ℝ × FieldPair d → ℂ,
      ∃ D : Fin d → ℝ × FieldPair d → ℂ,
      Measurable V ∧ Measurable Z ∧ (∀ j, Measurable (D j)) ∧
      (∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] P (s - a).toNNReal g) ∧
      (∀ s, (fun ω => Z (s, ω)) =ᵐ[reducedLaw Q] P (s - b).toNNReal h) ∧
      (∀ j s, (fun ω => D j (s, ω)) =ᵐ[reducedLaw Q] (hP.gradientOrbit g (s - a)) j) ∧
      (∀ s, a < s → HasDerivAt w (P (s - a).toNNReal g) s ∧
        IsComplexGeneratorPair Q i ζ (w s) (P (s - a).toNNReal g)) ∧
      (∀ s, b < s →
        HasDerivAt (fun r : ℝ => P (r - a).toNNReal g) (P (s - b).toNNReal h) s ∧
        IsComplexGeneratorPair Q i ζ (P (s - a).toNNReal g) (P (s - b).toNNReal h) ∧
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (P (s - a).toNNReal g) (hP.gradientOrbit g (s - a))) ∧
      (∀ᵐ ω ∂reducedLaw Q, ∀ n : ℕ, ∀ K : Set (Vec d), IsCompact K →
        MemLp (fun p : Vec d × ℝ => V (p.2, translate p.1 ω)) 2
          ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ)))) ∧
        MemLp (fun p : Vec d × ℝ => Z (p.2, translate p.1 ω)) 2
          ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ)))) ∧
        Integrable (fun p : Vec d × ℝ =>
          star (V (p.2, translate p.1 ω)) * Z (p.2, translate p.1 ω))
          ((volume.restrict K).prod (volume.restrict (Icc (0 : ℝ) (n : ℝ))))) ∧
      ∀ c e : ℝ, b < c → c < e → ∀ z : Vec d, ∀ r κ : ℝ,
        0 < r → 0 ≤ κ → r ≤ κ * Real.sqrt t / (1 + ‖ζ‖ * Real.sqrt t) →
        ∀ᵐ ω ∂reducedLaw Q,
          (∫ x in {x | euclideanNorm (x - z) ≤ r},
            ‖(P (e - a).toNNReal g) (translate x ω)‖ ^ 2) ≤
          2 * ((e - c)⁻¹ +
            (2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3) *
              ((κ ^ 2 + (d : ℝ) * B ^ 2) / r ^ 2)) *
            (∫ s in Icc c e, ∫ x in {x | euclideanNorm (x - z) ≤ 2 * r},
              ‖V (s, translate x ω)‖ ^ 2) := by
  obtain ⟨B, hB, hcutoff⟩ := exists_physical_euclidean_cutoff d
  refine ⟨B, hB, ?_⟩
  intro Λ₀ r₀ Q i ζ P hP f t a b ht ha hab L w
  let := reducedLaw_probability Q
  obtain ⟨g, h, V, Z, D, hV, hZ, hD, heV, heZ, heD, hw, hd, hlocal, henergy⟩ :=
    complexForced_correctedOrbit_derivative_ae_boundaryCutoffEnergy hP f ht ha hab
  refine ⟨g, h, V, Z, D, hV, hZ, hD, heV, heZ, heD, hw, hd, hlocal, ?_⟩
  let u : ℝ → Lp ℂ 2 (reducedLaw Q) := fun s => P (s - a).toNNReal g
  have hcontV : Continuous u :=
    (hP.2.2.1 g).comp (continuous_real_toNNReal.comp (continuous_id.sub continuous_const))
  have hL : 0 < L := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hC : 0 ≤ 2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3 := by positivity
  intro c e hc hce z r κ hr hκ hrad
  obtain ⟨φ, hφ, hφrange, hone, hzero, hφD⟩ := hcutoff z r hr
  obtain ⟨η, hη, hηd, hηb, hηc, hηbounds⟩ := exists_physical_temporal_cutoff hce
  have hηcont : ContinuousOn η (Icc c e) := by
    simpa only [uIcc_of_le hce.le] using hη.continuousOn
  have hηrange s (hs : s ∈ Icc c e) : 0 ≤ η s ∧ η s ≤ 1 ∧
      0 ≤ deriv η s ∧ deriv η s ≤ 2 / (e - c) :=
    ⟨(hηbounds s hs).1, (hηbounds s hs).2.1,
      (hηbounds s hs).2.2.1, (hηbounds s hs).2.2.2.1⟩
  have hwI : IntegrableOn (fun s => ‖u s‖ ^ 2) (Icc c e) volume :=
    (hcontV.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hlocalW := ae_locally_memLp_joint_spatial_translate
    (reducedLaw Q) (reducedLaw_stationary Q) hV
    (integrable_sq_joint_l2_representative hwI hV heV)
  have hlocalU := ae_complex_orbit_memLp_on_all_compacts
    (reducedLaw Q) (reducedLaw_stationary Q) (u e)
  filter_upwards [henergy c e hc hce.le φ hφ η hη hηd
    (fun s hs => (hηbounds s hs).1), hlocalW, hlocalU]
    with ω hω hlW hlU
  have hK := isCompact_physical_euclidean_closedBall z (2 * r)
  apply physical_timeSliceL2_of_cutoff_energy (D := fun j p => D j (p.2, translate p.1 ω))
    hce hr hκ hL hC hrad
    (hlW _ hK) (hlU _ hK) hφ hφrange hone hzero hφD hηcont hηd
    hηrange
  rw [hηb, hηc, zero_mul, one_mul, zero_sub] at hω
  linarith only [hω]

/-- Fixed-time derivative mass is controlled solely by corrected-orbit cylinder mass. -/
theorem local_time_uniform_corrected_orbit_derivative_timeSlice
    (d : ℕ) [Fact (2 ≤ d)] :
    ∃ B₀ B₁ B₂ B₃ T₁ T₂ : ℝ,
      0 < B₀ ∧ 0 < B₁ ∧ 0 < B₂ ∧ 0 < B₃ ∧ 0 < T₁ ∧ 0 < T₂ ∧
    ∀ {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t a b : ℝ}
    (_ht : 0 < t) (_ha : 0 < a) (_hab : a < b),
    let L := Real.exp (2 * Λ₀) * Λ₀
    let K := fun (B T Δt Δx : ℝ) =>
      4 * L * (T / Δt / 2 + (2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3) *
        (‖ζ‖ ^ 2 + (d : ℝ) * B ^ 2 / Δx ^ 2))
    let A := fun (B Δx ε : ℝ) =>
      (1 / (4 * ε) + 4 * ((d : ℝ) * B ^ 2 / Δx ^ 2)) *
        ((d : ℝ) ^ 2 * L ^ 2 / 4) + ‖ζ‖ ^ 2 * ((d : ℝ) * L ^ 2)
    let H := fun (Δt r κ : ℝ) => Δt⁻¹ +
      (2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3) *
        ((κ ^ 2 + (d : ℝ) * B₃ ^ 2) / r ^ 2)
    let w := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
    ∃ g : Lp ℂ 2 (reducedLaw Q), ∃ W V : ℝ × FieldPair d → ℂ,
      Measurable W ∧ Measurable V ∧
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] w s) ∧
      (∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] P (s - a).toNNReal g) ∧
      (∀ s, a < s → HasDerivAt w (P (s - a).toNNReal g) s ∧
        IsComplexGeneratorPair Q i ζ (w s) (P (s - a).toNNReal g)) ∧
      ∀ c e v : ℝ, b < c → c < e → e < v → ∀ z : Vec d, ∀ r R κ : ℝ,
        0 < r → 2 * r < R → 0 ≤ κ →
        r ≤ κ * Real.sqrt t / (1 + ‖ζ‖ * Real.sqrt t) → ∀ᵐ ω ∂reducedLaw Q,
          (∫ x in {x | euclideanNorm (x - z) ≤ r},
            ‖(P (v - a).toNNReal g) (translate x ω)‖ ^ 2) ≤
          8 * H (v - e) r κ * A B₀ ((R - 2 * r) / 4)
              (1 / (64 * K B₁ T₁ (3 * (e - c) / 4) ((R - 2 * r) / 4))) *
            K B₂ T₂ (3 * (e - c) / 4) ((R - 2 * r) / 4) *
            (∫ s in Icc c v, ∫ x in {x | euclideanNorm (x - z) ≤ R},
              ‖W (s, translate x ω)‖ ^ 2) := by
  obtain ⟨B₀, B₁, B₂, T₁, T₂, hB₀, hB₁, hB₂, hT₁, hT₂, hcylinder⟩ :=
    local_time_uniform_corrected_orbit_derivative_cylinder d
  obtain ⟨B₃, hB₃, hslice⟩ := local_time_uniform_restarted_derivative_timeSliceL2 d
  refine ⟨B₀, B₁, B₂, B₃, T₁, T₂, hB₀, hB₁, hB₂, hB₃, hT₁, hT₂, ?_⟩
  intro Λ₀ r₀ Q i ζ P hP f t a b ht ha hab L K A H w
  obtain ⟨g, W, V, hW, hV, heW, heV, hregular, hcyl⟩ := hcylinder hP f ht ha hab
  obtain ⟨g', h, V', Z, D, hV', hZ, hD, heV', heZ, heD, hw', hd, hlocal, hts⟩ :=
    hslice hP f ht ha hab
  have hg : g = g' := hP.restart_derivative_unique
    (fun s hs => (hregular s hs).1) (fun s hs => (hw' s hs).1)
  subst g'
  refine ⟨g, W, V, hW, hV, heW, heV, hregular, ?_⟩
  intro c e v hc hce hev z r R κ hr hrR hκ hrad
  have he : b < e := hc.trans hce
  have hmass := local_time_physical_cylinder_integral_congr
    (κ := Unit) (fun _ => hV') (fun _ => hV)
    (fun _ s => (heV' s).trans (heV s).symm)
    (fun u => ‖u ()‖ ^ 2) (Icc e v) {x | euclideanNorm (x - z) ≤ 2 * r}
  have hL : 0 < L := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter)
  have hH : 0 ≤ 2 * H (v - e) r κ := by
    dsimp [H]
    positivity
  filter_upwards [hts e v he hev z r κ hr hκ hrad,
    hcyl c e v hc hce hev.le z (2 * r) R (by positivity) hrR, hmass]
    with ω htime hcy hm
  rw [hm] at htime
  have h := htime.trans (mul_le_mul_of_nonneg_left hcy hH)
  convert h using 1
  ring

/-- Algebraic coefficient control at every radius at least the parabolic scale. -/
theorem local_time_large_radius_coefficient
    {L N Z B₀ B₁ B₂ B₃ T₁ T₂ t r : ℝ}
    (hL : 0 ≤ L) (hN : 0 ≤ N) (hZ : 0 ≤ Z)
    (hT₁ : 0 ≤ T₁) (hT₂ : 0 ≤ T₂) (ht : 0 < t) (hr : 0 < r)
    (htr : t ≤ r ^ 2) :
    let C := 2 * N * (N + 1) * L ^ 3
    let U := (1 + Z * Real.sqrt t) ^ 2 / t
    let K := fun (B T Δt Δx : ℝ) =>
      4 * L * (T / Δt / 2 + C * (Z ^ 2 + N * B ^ 2 / Δx ^ 2))
    let A := fun (B Δx ε : ℝ) =>
      (1 / (4 * ε) + 4 * (N * B ^ 2 / Δx ^ 2)) *
        (N ^ 2 * L ^ 2 / 4) + Z ^ 2 * (N * L ^ 2)
    let Kc := fun B T : ℝ => 4 * L * (8 * T / 3 + C * (1 + 4 * N * B ^ 2))
    let Ac := (16 * Kc B₁ T₁ + 16 * N * B₀ ^ 2) * (N ^ 2 * L ^ 2 / 4) + N * L ^ 2
    let Hc := 2 + C * (1 + N * B₃ ^ 2)
    8 * (2 / t + C * (U + N * B₃ ^ 2 / r ^ 2)) *
        A B₀ (r / 2) (1 / (64 * K B₁ T₁ (3 * t / 16) (r / 2))) *
        K B₂ T₂ (3 * t / 16) (r / 2) ≤
      (8 * Hc * Ac * Kc B₂ T₂) * (1 + Z * Real.sqrt t) ^ 6 / t ^ 3 := by
  intro C U K A Kc Ac Hc
  have hs : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have hs2 : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt ht.le
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hi : 1 / t ≤ U := by
    apply (div_le_div_iff_of_pos_right ht).mpr
    nlinarith [mul_nonneg hZ hs]
  have hZt : Z ^ 2 * t ≤ (1 + Z * Real.sqrt t) ^ 2 := by
    nlinarith [mul_nonneg hZ hs, sq_nonneg (Z * Real.sqrt t)]
  have hz : Z ^ 2 ≤ U := (le_div_iff₀ ht).mpr hZt
  have hir : 1 / r ^ 2 ≤ U :=
    (one_div_le_one_div_of_le ht htr).trans hi
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hK (B T : ℝ) : K B T (3 * t / 16) (r / 2) =
      4 * L * ((8 * T / 3) * (1 / t) + C * (Z ^ 2 + 4 * N * B ^ 2 * (1 / r ^ 2))) := by
    dsimp [K]
    field_simp
    ring
  have hKle (B T : ℝ) (hT : 0 ≤ T) :
      K B T (3 * t / 16) (r / 2) ≤ Kc B T * U := by
    rw [hK]
    calc
      _ ≤ 4 * L * ((8 * T / 3) * U + C * (U + 4 * N * B ^ 2 * U)) := by
        gcongr
      _ = _ := by dsimp [Kc]; ring
  have hinv (k : ℝ) : 1 / (4 * (1 / (64 * k))) = 16 * k := by
    simp only [one_div, mul_inv_rev, inv_inv]
    ring
  have hA : A B₀ (r / 2) (1 / (64 * K B₁ T₁ (3 * t / 16) (r / 2))) =
      (16 * K B₁ T₁ (3 * t / 16) (r / 2) + 16 * N * B₀ ^ 2 * (1 / r ^ 2)) *
        (N ^ 2 * L ^ 2 / 4) + Z ^ 2 * (N * L ^ 2) := by
    dsimp [A]
    rw [hinv]
    field_simp
    ring
  have hAle : A B₀ (r / 2) (1 / (64 * K B₁ T₁ (3 * t / 16) (r / 2))) ≤ Ac * U := by
    rw [hA]
    calc
      _ ≤ (16 * (Kc B₁ T₁ * U) + 16 * N * B₀ ^ 2 * U) *
          (N ^ 2 * L ^ 2 / 4) + U * (N * L ^ 2) := by
        gcongr
        exact hKle B₁ T₁ hT₁
      _ = _ := by dsimp [Ac]; ring
  have hHle : 2 / t + C * (U + N * B₃ ^ 2 / r ^ 2) ≤ Hc * U := by
    calc
      _ = 2 * (1 / t) + C * (U + N * B₃ ^ 2 * (1 / r ^ 2)) := by ring
      _ ≤ 2 * U + C * (U + N * B₃ ^ 2 * U) := by gcongr
      _ = _ := by dsimp [Hc]; ring
  have hKpos : 0 ≤ K B₂ T₂ (3 * t / 16) (r / 2) := by dsimp [K]; positivity
  have hApos : 0 ≤ A B₀ (r / 2) (1 / (64 * K B₁ T₁ (3 * t / 16) (r / 2))) := by
    rw [hA]
    dsimp [K]
    positivity
  calc
    _ ≤ 8 * (Hc * U) * (Ac * U) * (Kc B₂ T₂ * U) := by
      gcongr
      exact hKle B₂ T₂ hT₂
    _ = _ := by dsimp [U]; field_simp

/-- Uniform parabolic-scale bound with no derivative mass on the right. -/
theorem local_time_uniform_corrected_orbit_derivative_largeRadius
    (d : ℕ) [Fact (2 ≤ d)] (Λ₀ : ℝ) (hΛ : 1 ≤ Λ₀) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
    ∀ {r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t a b : ℝ}
    (_ht : 0 < t) (_ha : 0 < a) (_hab : a < b),
    let w := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
    ∃ g : Lp ℂ 2 (reducedLaw Q), ∃ W V : ℝ × FieldPair d → ℂ,
      Measurable W ∧ Measurable V ∧
      (∀ s, (fun ω => W (s, ω)) =ᵐ[reducedLaw Q] w s) ∧
      (∀ s, (fun ω => V (s, ω)) =ᵐ[reducedLaw Q] P (s - a).toNNReal g) ∧
      (∀ s, a < s → HasDerivAt w (P (s - a).toNNReal g) s ∧
        IsComplexGeneratorPair Q i ζ (w s) (P (s - a).toNNReal g)) ∧
      ∀ (_hb : b < t / 4), ∀ z : Vec d, ∀ r : ℝ, Real.sqrt t ≤ r → ∀ᵐ ω ∂reducedLaw Q,
        (∫ x in {x | euclideanNorm (x - z) ≤ r},
          ‖(P (t - a).toNNReal g) (translate x ω)‖ ^ 2) ≤
        (C₀ * (1 + ‖ζ‖ * Real.sqrt t) ^ 6 / t ^ 3) *
          (∫ s in Icc (t / 4) t, ∫ x in {x | euclideanNorm (x - z) ≤ 4 * r},
            ‖W (s, translate x ω)‖ ^ 2) := by
  obtain ⟨B₀, B₁, B₂, B₃, T₁, T₂, hB₀, hB₁, hB₂, hB₃, hT₁, hT₂, hproducer⟩ :=
    local_time_uniform_corrected_orbit_derivative_timeSlice d
  let L := Real.exp (2 * Λ₀) * Λ₀
  let C := 2 * (d : ℝ) * ((d : ℝ) + 1) * L ^ 3
  let Kc := fun B T : ℝ => 4 * L * (8 * T / 3 + C * (1 + 4 * (d : ℝ) * B ^ 2))
  let Ac := (16 * Kc B₁ T₁ + 16 * (d : ℝ) * B₀ ^ 2) *
    ((d : ℝ) ^ 2 * L ^ 2 / 4) + (d : ℝ) * L ^ 2
  let Hc := 2 + C * (1 + (d : ℝ) * B₃ ^ 2)
  let C₀ := 8 * Hc * Ac * Kc B₂ T₂
  have hdNat : 2 ≤ d := Fact.out
  have hd : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hL : 0 < L := mul_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one hΛ)
  have hC₀ : 0 < C₀ := by dsimp [C₀, Hc, Ac, Kc, C]; positivity
  refine ⟨C₀, hC₀, ?_⟩
  intro r₀ Q i ζ P hP f t a b ht ha hab w
  obtain ⟨g, W, V, hW, hV, heW, heV, hregular, hbound⟩ := hproducer hP f ht ha hab
  refine ⟨g, W, V, hW, hV, heW, heV, hregular, ?_⟩
  intro hb z r hrad
  have hr : 0 < r := (Real.sqrt_pos.mpr ht).trans_le hrad
  have htr : t ≤ r ^ 2 := by
    calc
      t = (Real.sqrt t) ^ 2 := (Real.sq_sqrt ht.le).symm
      _ ≤ r ^ 2 := (sq_le_sq₀ (Real.sqrt_nonneg t) hr.le).mpr hrad
  let κ := r * (1 + ‖ζ‖ * Real.sqrt t) / Real.sqrt t
  have hκ : 0 ≤ κ := by dsimp [κ]; positivity
  have hrad' : r ≤ κ * Real.sqrt t / (1 + ‖ζ‖ * Real.sqrt t) := by
    apply le_of_eq
    dsimp [κ]
    field_simp
  have hs := hbound (t / 4) (t / 2) t hb (by linarith) (by linarith)
    z r (4 * r) κ hr (by linarith) hκ hrad'
  have hspace : (4 * r - 2 * r) / 4 = r / 2 := by ring
  have htime : 3 * (t / 2 - t / 4) / 4 = 3 * t / 16 := by ring
  have hκsq : κ ^ 2 / r ^ 2 = (1 + ‖ζ‖ * Real.sqrt t) ^ 2 / t := by
    dsimp [κ]
    rw [div_pow, mul_pow, Real.sq_sqrt ht.le]
    field_simp
  have hH : (t - t / 2)⁻¹ + C * ((κ ^ 2 + (d : ℝ) * B₃ ^ 2) / r ^ 2) =
      2 / t + C * ((1 + ‖ζ‖ * Real.sqrt t) ^ 2 / t + (d : ℝ) * B₃ ^ 2 / r ^ 2) := by
    rw [add_div, hκsq]
    congr 1
    field_simp
    norm_num
  have hcoeff := local_time_large_radius_coefficient hL.le hd.le (norm_nonneg ζ)
    hT₁.le hT₂.le ht hr htr (B₀ := B₀) (B₁ := B₁) (B₂ := B₂) (B₃ := B₃)
  filter_upwards [hs] with ω hω
  rw [hspace, htime, hH] at hω
  exact hω.trans (mul_le_mul_of_nonneg_right hcoeff (by positivity))

/-- The normalization cost of enlarging an actual Euclidean spatial window
is dimension-only, with the coordinate Lebesgue measure retained. -/
theorem local_time_window_volume_dilation {d : ℕ} (z : Vec d)
    {ρ k : ℝ} (hρ : 0 < ρ) (hk : 0 < k) :
    volume.real {y : Vec d | euclideanNorm (y - z) < k * ρ} =
      k ^ d * volume.real {y : Vec d | euclideanNorm (y - z) < ρ} := by
  have htranslate (r : ℝ) :
      volume.real {y : Vec d | euclideanNorm (y - z) < r} =
        volume.real (External.AKM.ball (0 : Vec d) r) := by
    unfold Measure.real
    congr 1
    simpa only [External.AKM.ball, sub_zero, sub_eq_add_neg, Set.preimage_ofPred_eq, neg_zero, add_zero] using
      measure_preimage_add_right (volume : Measure (Vec d)) (-z)
        (External.AKM.ball (0 : Vec d) r)
  rw [htranslate, htranslate, Correctors.paired_ball_volume_scale (mul_pos hk hρ),
    Correctors.paired_ball_volume_scale hρ, mul_pow]
  ring

/-- Equality of joint representatives only on the time window suffices for
physical cylinder integrals over that window. -/
theorem local_time_physical_cylinder_integral_congr_on
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀}
    {F H : ℝ × FieldPair d → ℂ} (hF : Measurable F) (hH : Measurable H)
    {J : Set ℝ} (hJ : MeasurableSet J)
    (he : ∀ s ∈ J, (fun ω => F (s, ω)) =ᵐ[reducedLaw Q] fun ω => H (s, ω))
    (S : Set (Vec d)) :
    ∀ᵐ ω ∂reducedLaw Q,
      (∫ s in J, ∫ x in S, ‖F (s, translate x ω)‖ ^ 2) =
        ∫ s in J, ∫ x in S, ‖H (s, translate x ω)‖ ^ 2 := by
  classical
  let F' : ℝ × FieldPair d → ℂ := fun p => if p.1 ∈ J then F p else 0
  let H' : ℝ × FieldPair d → ℂ := fun p => if p.1 ∈ J then H p else 0
  have hF' : Measurable F' := hF.piecewise (hJ.preimage measurable_fst) measurable_const
  have hH' : Measurable H' := hH.piecewise (hJ.preimage measurable_fst) measurable_const
  have he' (s : ℝ) : (fun ω => F' (s, ω)) =ᵐ[reducedLaw Q] fun ω => H' (s, ω) := by
    by_cases hs : s ∈ J
    · simpa only [F', H', ite_eq_left hs] using he s hs
    · exact ae_of_all _ fun ω => by simp only [F', H', ite_eq_right hs]
  have heq := local_time_physical_cylinder_integral_congr (Q := Q) (κ := Unit)
    (F := fun _ => F') (H := fun _ => H') (fun _ => hF') (fun _ => hH')
    (fun _ => he') (fun f => ‖f ()‖ ^ 2) J S
  filter_upwards [heq] with ω hω
  have hchange (K : ℝ × FieldPair d → ℂ) :
      (∫ s in J, ∫ x in S, ‖(if s ∈ J then K (s, translate x ω) else 0)‖ ^ 2) =
        ∫ s in J, ∫ x in S, ‖K (s, translate x ω)‖ ^ 2 := by
    apply setIntegral_congr_fun hJ
    intro s hs
    simp only [ite_eq_left hs]
  exact (hchange F).symm.trans (hω.trans (hchange H))

/-- Convert an unnormalized derivative-mass estimate to the actual normalized
space-time cylinder, retaining the time-window length and spatial dilation. -/
theorem local_time_cylinder_mass_normalization {d : ℕ} (z : Vec d)
    {t ρ K : ℝ} (ht : 0 < t) (hρ : 0 < ρ)
    (v : Vec d → ℂ) (W : ℝ × Vec d → ℂ)
    (hmass : (∫ x in {x | euclideanNorm (x - z) < ρ}, ‖v x‖ ^ 2) ≤
      K * ∫ s in Icc (t / 4) t,
        ∫ x in {x | euclideanNorm (x - z) < 8 * ρ}, ‖W (s, x)‖ ^ 2) :
    t * (⨍ x in {x | euclideanNorm (x - z) < ρ}, ‖v x‖ ^ 2) ≤
      (3 * t ^ 2 / 4) * (8 : ℝ) ^ d * K *
        (⨍ s in Icc (t / 4) t,
          ⨍ x in {x | euclideanNorm (x - z) < 8 * ρ}, ‖W (s, x)‖ ^ 2) := by
  have hvol := localSpatialEnergy_window_volume z ρ hρ
  have hscale := local_time_window_volume_dilation z hρ (show (0 : ℝ) < 8 by norm_num)
  have htime : t - t / 4 = 3 * t / 4 := by ring
  have havg :
      (⨍ s in Icc (t / 4) t,
        ⨍ x in {x | euclideanNorm (x - z) < 8 * ρ}, ‖W (s, x)‖ ^ 2) =
      (3 * t / 4)⁻¹ *
        ((8 : ℝ) ^ d * volume.real {x | euclideanNorm (x - z) < ρ})⁻¹ *
        (∫ s in Icc (t / 4) t,
          ∫ x in {x | euclideanNorm (x - z) < 8 * ρ}, ‖W (s, x)‖ ^ 2) := by
    simp only [average_eq, measureReal_restrict_apply_univ, smul_eq_mul]
    rw [Real.volume_real_Icc_of_le (by linarith), htime, hscale, integral_const_mul]
    ring
  calc
    _ = (t / volume.real {x | euclideanNorm (x - z) < ρ}) *
        (∫ x in {x | euclideanNorm (x - z) < ρ}, ‖v x‖ ^ 2) := by
      simp only [average_eq, measureReal_restrict_apply_univ, smul_eq_mul, div_eq_mul_inv]
      ring
    _ ≤ (t / volume.real {x | euclideanNorm (x - z) < ρ}) *
        (K * ∫ s in Icc (t / 4) t,
          ∫ x in {x | euclideanNorm (x - z) < 8 * ρ}, ‖W (s, x)‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by
      rw [havg]
      field_simp [ht.ne', hvol.ne']

/-- The supplied corrected-cylinder estimate applies to the actual scalar source.
Gradient uniqueness identifies the source on positive times, including the entire
primitive interval used by a positive-time corrected orbit. -/
theorem local_time_corrected_cylinder_of_source_dependency
    (h0 : node_l_u3A_forced_u2D_local_u23_centered_u2D_sourceStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℝ, 2 ≤ p → ∃ Cp : ℝ, 0 < Cp ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (ζ : ℂ)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)),
    MemLp f (ENNReal.ofReal p) (reducedLaw Q) →
    let u := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f))
    ∀ t : ℝ, 0 < t →
      MemLp (u (t / 8)) (ENNReal.ofReal p) (reducedLaw Q) ∧
      IntegrableOn (hP.centeringSource f) (Icc (t / 4) t) ∧
      (∀ r ∈ Icc (t / 4) t,
        ‖hP.centeringSource f r‖ ≤ C * ‖ζ‖ / Real.sqrt t *
          Real.exp (C * ‖ζ‖ ^ 2 * t) * ‖u (t / 8)‖) ∧
      (let w := fun r : ℝ => u r +
          Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
       ∃ U : ℝ × FieldPair d → ℂ,
         StronglyMeasurable U ∧
         (∀ r : ℝ, 0 < r → (fun ω => U (r, ω)) =ᵐ[reducedLaw Q] w r) ∧
         ∀ (x : Vec d) (ρ : ℝ), 0 < ρ →
           let N := fun ω : FieldPair d => Real.sqrt
             (⨍ r in Icc (t / 4) t,
               ⨍ y in {y : Vec d | euclideanNorm (y - x) < ρ},
                 ‖U (r, translate y ω)‖ ^ 2)
           MemLp N (ENNReal.ofReal p) (reducedLaw Q) ∧
           eLpNorm N (ENNReal.ofReal p) (reducedLaw Q) ≤
             ENNReal.ofReal (Cp * (1 + ‖ζ‖ * Real.sqrt t) *
               Real.exp (Cp * ‖ζ‖ ^ 2 * t)) *
             eLpNorm (u (t / 8)) (ENNReal.ofReal p) (reducedLaw Q)) := by
  obtain ⟨C, hC, hinput⟩ := h0 d hd D
  refine ⟨C, hC, ?_⟩
  intro p hp
  obtain ⟨Cp, hCp, hinput⟩ := hinput p hp
  refine ⟨Cp, hCp, ?_⟩
  intro Q hQ ζ P hP f hf u
  let := reducedLaw_probability Q
  obtain ⟨G, hG, hwindow⟩ := hinput Q hQ ζ P hP f hf
  let c := fun r : ℝ => ζ * (∫ ω,
    ∑ j : Fin d, (ω.1 0 j ⟨0, by omega⟩ : ℂ) * G r j ω ∂reducedLaw Q)
  have hc : ∀ r : ℝ, 0 < r → c r = hP.centeringSource f r := by
    intro r hr
    have hactual : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (u r) (hP.gradientOrbit f r) := by
      simpa only [IsComplexEnvironmentSemigroup.gradientOrbit, dite_eq_left hr] using
        hP.forcedGradient_centered_spec r.toNNReal (by simpa using hr) f
    have he : G r = hP.gradientOrbit f r :=
      WithLp.ofLp_injective 2 ((hG r hr).1.unique hactual)
    change ζ * (∫ ω, ∑ j, (ω.1 0 j ⟨0, by omega⟩ : ℂ) * G r j ω
      ∂reducedLaw Q) = _
    rw [he]
    rfl
  intro t ht
  obtain ⟨hmem, hint, hbound, _, U, hU, hrep, hmoment⟩ := hwindow t ht
  have hpos : ∀ r ∈ Icc (t / 4) t, 0 < r := by
    intro r hr
    linarith [hr.1]
  refine ⟨hmem, hint.congr_fun (fun r hr => hc r (hpos r hr)) measurableSet_Icc,
    ?_, U, hU, ?_, hmoment⟩
  · intro r hr
    simpa only [← hc r (hpos r hr)] using hbound r hr
  · intro r hr
    have hprimitive : (∫ v in (t / 4)..r, c v) =
        ∫ v in (t / 4)..r, hP.centeringSource f v := by
      apply intervalIntegral.integral_congr
      intro v hv
      apply hc v
      have hmin : 0 < min (t / 4) r := lt_min (by linarith) hr
      exact hmin.trans_le hv.1
    have hre := hrep r
    change (fun ω => U (r, ω)) =ᵐ[reducedLaw Q]
      (u r + Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, c v) :
        Lp ℂ 2 (reducedLaw Q)) at hre
    rw [hprimitive] at hre
    exact hre

/-- The actual corrected derivative is controlled by any positive-time joint
representative of the corrected orbit, in the normalized cylinder used by h0. -/
theorem local_time_uniform_corrected_derivative_normalized_cylinder
    (d : ℕ) [Fact (2 ≤ d)] (Λ₀ : ℝ) (hΛ : 1 ≤ Λ₀) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
    ∀ {r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {t a b : ℝ}
    (_ht : 0 < t) (_ha : 0 < a) (_hab : a < b),
    let w := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f)) +
      Lp.const 2 (reducedLaw Q) (∫ v in (t / 4)..r, hP.centeringSource f v)
    ∀ U : ℝ × FieldPair d → ℂ, Measurable U →
      (∀ s, 0 < s → (fun ω => U (s, ω)) =ᵐ[reducedLaw Q] w s) →
    ∃ g : Lp ℂ 2 (reducedLaw Q),
      (∀ s, a < s → HasDerivAt w (P (s - a).toNNReal g) s ∧
        IsComplexGeneratorPair Q i ζ (w s) (P (s - a).toNNReal g)) ∧
      ∀ (_hb : b < t / 4), ∀ z : Vec d, ∀ ρ : ℝ, Real.sqrt t ≤ ρ →
        ∀ᵐ ω ∂reducedLaw Q,
          t * (⨍ x in {x | euclideanNorm (x - z) < ρ},
            ‖(P (t - a).toNNReal g) (translate x ω)‖ ^ 2) ≤
          (C₀ * (1 + ‖ζ‖ * Real.sqrt t) ^ 6 / t) *
            (⨍ s in Icc (t / 4) t,
              ⨍ x in {x | euclideanNorm (x - z) < 8 * ρ},
                ‖U (s, translate x ω)‖ ^ 2) := by
  obtain ⟨C, hC, hproducer⟩ :=
    local_time_uniform_corrected_orbit_derivative_largeRadius d Λ₀ hΛ
  refine ⟨3 * (8 : ℝ) ^ d * C / 4, by positivity, ?_⟩
  intro r₀ Q i ζ P hP f t a b ht ha hab w U hU heU
  let := reducedLaw_probability Q
  obtain ⟨g, W, V, hW, _, heW, _, hregular, hmass⟩ := hproducer hP f ht ha hab
  refine ⟨g, hregular, ?_⟩
  intro hb z ρ hrad
  have hρ : 0 < ρ := (Real.sqrt_pos.mpr ht).trans_le hrad
  have hu : Continuous (fun s : ℝ =>
      centeredComplexLp Q (P s.toNNReal (centeredComplexLp Q f))) := by
    simpa only [Function.comp_def, centeredComplexLpCLM_apply] using
      (centeredComplexLpCLM Q).continuous.comp
        ((hP.2.2.1 (centeredComplexLp Q f)).comp continuous_real_toNNReal)
  have hw : Continuous w := hu.add ((Lp.constL 2 (reducedLaw Q) ℂ).continuous.comp
    (Blueprint.continuous_centered_source_primitive hP f (t / 4)))
  have hlocalW := ae_locally_memLp_joint_spatial_translate
    (reducedLaw Q) (reducedLaw_stationary Q) hW
    (integrable_sq_joint_l2_representative
      ((hw.norm.pow 2).continuousOn.integrableOn_compact
        (μ := (volume : Measure ℝ)) (K := Icc (t / 4) t) isCompact_Icc) hW heW)
  have hlocalv := ae_complex_orbit_memLp_on_all_compacts
    (reducedLaw Q) (reducedLaw_stationary Q) (P (t - a).toNNReal g)
  have heq := local_time_physical_cylinder_integral_congr_on
    (J := Icc (t / 4) t) hW hU measurableSet_Icc
    (fun s hs => (heW s).trans (heU s (by linarith [hs.1])).symm)
    {x | euclideanNorm (x - z) < 8 * ρ}
  filter_upwards [hmass hb z ρ hrad, hlocalW, hlocalv, heq] with ω hmass hlocW hlocv heq
  have hiv := (memLp_two_iff_integrable_sq_norm
    (hlocv _ (isCompact_physical_euclidean_closedBall z ρ)).aestronglyMeasurable).mp
      (hlocv _ (isCompact_physical_euclidean_closedBall z ρ))
  have hiW := (memLp_two_iff_integrable_sq_norm
    (hlocW _ (isCompact_physical_euclidean_closedBall z (8 * ρ))).aestronglyMeasurable).mp
      (hlocW _ (isCompact_physical_euclidean_closedBall z (8 * ρ)))
  have hiWopen : Integrable
      (fun p : Vec d × ℝ => ‖W (p.2, translate p.1 ω)‖ ^ 2)
      ((volume.restrict {x | euclideanNorm (x - z) < 8 * ρ}).prod
        (volume.restrict (Icc (t / 4) t))) :=
    hiW.mono_measure (Measure.prod_mono
      (Measure.restrict_mono (fun x (hx : euclideanNorm (x - z) < 8 * ρ) =>
        show euclideanNorm (x - z) ≤ 8 * ρ from hx.le) le_rfl) le_rfl)
  have hleft : (∫ x in {x | euclideanNorm (x - z) < ρ},
        ‖(P (t - a).toNNReal g) (translate x ω)‖ ^ 2) ≤
      ∫ x in {x | euclideanNorm (x - z) ≤ ρ},
        ‖(P (t - a).toNNReal g) (translate x ω)‖ ^ 2 :=
    setIntegral_mono_set hiv (ae_of_all _ fun _ => sq_nonneg _)
      (ae_of_all _ fun x (hx : euclideanNorm (x - z) < ρ) =>
        show euclideanNorm (x - z) ≤ ρ from hx.le)
  have hright := local_time_cylinder_integral_mono
    (S := {x | euclideanNorm (x - z) ≤ 4 * ρ})
    (K := {x | euclideanNorm (x - z) < 8 * ρ})
    (fun x (hx : euclideanNorm (x - z) ≤ 4 * ρ) =>
      show euclideanNorm (x - z) < 8 * ρ by linarith) (Subset.refl _) hiWopen (fun _ => sq_nonneg _)
  have hraw : (∫ x in {x | euclideanNorm (x - z) < ρ},
        ‖(P (t - a).toNNReal g) (translate x ω)‖ ^ 2) ≤
      (C * (1 + ‖ζ‖ * Real.sqrt t) ^ 6 / t ^ 3) *
        (∫ s in Icc (t / 4) t,
          ∫ x in {x | euclideanNorm (x - z) < 8 * ρ}, ‖U (s, translate x ω)‖ ^ 2) := by
    rw [← heq]
    exact hleft.trans (hmass.trans (mul_le_mul_of_nonneg_left hright (by positivity)))
  have hn := local_time_cylinder_mass_normalization z ht hρ
    (fun x => (P (t - a).toNNReal g) (translate x ω))
    (fun p => U (p.1, translate p.2 ω)) hraw
  have hcoeff : (3 * t ^ 2 / 4) * (8 : ℝ) ^ d *
      (C * (1 + ‖ζ‖ * Real.sqrt t) ^ 6 / t ^ 3) =
      ((3 * (8 : ℝ) ^ d * C / 4) * (1 + ‖ζ‖ * Real.sqrt t) ^ 6 / t) := by
    field_simp
  rwa [hcoeff] at hn

/-- A zero gradient contributes zero to the physical energy, after passing
its `Lp` representative through the stationary spatial orbit. -/
theorem local_time_zero_gradient_energy_sq
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (t : ℝ≥0) (ρ : ℝ) (hρ : 0 < ρ) (z : Vec d)
    (v : Lp ℂ 2 (reducedLaw Q)) :
    ∀ᵐ ω ∂reducedLaw Q,
      localSpatialEnergy Q t ρ hρ z 0 v ω ^ 2 =
        (t : ℝ) * (⨍ x in {x | euclideanNorm (x - z) < ρ},
          ‖v (translate x ω)‖ ^ 2) := by
  let := reducedLaw_probability Q
  have hz : (fun ω => ‖(0 : Lp ℂ 2 (reducedLaw Q)) ω‖) =ᵐ[reducedLaw Q]
      fun _ => (0 : ℝ) := by
    filter_upwards [Lp.coeFn_zero ℂ 2 (reducedLaw Q)] with ω hω
    simp
  have hphys := ae_ae_stationary_orbit_eq (reducedLaw_stationary Q)
    (Lp.stronglyMeasurable (0 : Lp ℂ 2 (reducedLaw Q))).measurable.norm
    measurable_const hz
  filter_upwards [hphys] with ω hω
  rw [localSpatialEnergy_sq]
  have he : (∫ x in {x | euclideanNorm (x - z) < ρ},
      (∑ j : Fin d, ‖(0 : Fin d → Lp ℂ 2 (reducedLaw Q)) j (translate x ω)‖ ^ 2) +
        (t : ℝ) * ‖v (translate x ω)‖ ^ 2) =
      ∫ x in {x | euclideanNorm (x - z) < ρ}, (t : ℝ) * ‖v (translate x ω)‖ ^ 2 := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hω] with x hx
    simp
  simp only [average_eq, measureReal_restrict_apply_univ, smul_eq_mul]
  rw [he, integral_const_mul]
  ring

/-- A square estimate for the actual derivative energy transfers finite moments
from a nonnegative cylinder observable, retaining its explicit coefficient. -/
theorem local_time_zero_gradient_moment_of_sq_bound
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (t : ℝ≥0) (ρ : ℝ) (hρ : 0 < ρ) (z : Vec d)
    (v : Lp ℂ 2 (reducedLaw Q)) {p : ℝ≥0∞} {N : FieldPair d → ℝ}
    (hN : MemLp N p (reducedLaw Q)) (hNpos : ∀ᵐ ω ∂reducedLaw Q, 0 ≤ N ω)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ᵐ ω ∂reducedLaw Q,
      (t : ℝ) * (⨍ x in {x | euclideanNorm (x - z) < ρ},
        ‖v (translate x ω)‖ ^ 2) ≤ K * N ω ^ 2) :
    MemLp (localSpatialEnergy Q t ρ hρ z 0 v) p (reducedLaw Q) ∧
      eLpNorm (localSpatialEnergy Q t ρ hρ z 0 v) p (reducedLaw Q) ≤
        ENNReal.ofReal (Real.sqrt K) * eLpNorm N p (reducedLaw Q) := by
  have hm := localSpatialEnergy_aestronglyMeasurable Q t ρ hρ z 0 v
  have he : ∀ᵐ ω ∂reducedLaw Q,
      ‖localSpatialEnergy Q t ρ hρ z 0 v ω‖ ≤ Real.sqrt K * ‖N ω‖ := by
    filter_upwards [local_time_zero_gradient_energy_sq Q t ρ hρ z v,
      hbound, hNpos] with ω hsq hb hn
    have hpos : 0 ≤ localSpatialEnergy Q t ρ hρ z 0 v ω := Real.sqrt_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hpos, Real.norm_eq_abs, abs_of_nonneg hn]
    apply (sq_le_sq₀ hpos (mul_nonneg (Real.sqrt_nonneg _) hn)).mp
    rw [mul_pow, Real.sq_sqrt hK, hsq]
    exact hb
  exact ⟨hN.of_le_mul hm he, eLpNorm_le_mul_eLpNorm_of_ae_le_mul hm he p⟩

/-- The centered-source dependency supplies the finite moments of the actual
corrected forward time derivative, uniformly over all large physical balls. -/
theorem local_time_corrected_derivative_moment_of_source_dependency
    (h0 : node_l_u3A_forced_u2D_local_u23_centered_u2D_sourceStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ p : ℝ, 2 ≤ p → ∃ Cp : ℝ, 0 < Cp ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (ζ : ℂ)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)),
    MemLp f (ENNReal.ofReal p) (reducedLaw Q) →
    ∀ (t : ℝ≥0) (ht : 0 < (t : ℝ)),
    let u := fun r : ℝ => centeredComplexLp Q (P r.toNNReal (centeredComplexLp Q f))
    let w := fun r : ℝ => u r +
      Lp.const 2 (reducedLaw Q) (∫ s in ((t : ℝ) / 4)..r, hP.centeringSource f s)
    MemLp (u ((t : ℝ) / 8)) (ENNReal.ofReal p) (reducedLaw Q) ∧
    ∃ v : Lp ℂ 2 (reducedLaw Q), HasDerivAt w v (t : ℝ) ∧
      ∀ (ρ : ℝ) (z : Vec d) (hρ : Real.sqrt (t : ℝ) ≤ ρ),
        MemLp (localSpatialEnergy Q t ρ ((Real.sqrt_pos.mpr ht).trans_le hρ)
          z 0 v) (ENNReal.ofReal p) (reducedLaw Q) ∧
        eLpNorm (localSpatialEnergy Q t ρ ((Real.sqrt_pos.mpr ht).trans_le hρ)
          z 0 v) (ENNReal.ofReal p) (reducedLaw Q) ≤
          ENNReal.ofReal (Real.sqrt (C₀ * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ 6 / (t : ℝ))) *
            (ENNReal.ofReal (Cp * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) *
              Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ))) *
              eLpNorm (u ((t : ℝ) / 8)) (ENNReal.ofReal p) (reducedLaw Q)) := by
  let : Fact (2 ≤ d) := ⟨hd⟩
  obtain ⟨C₀, hC₀, hderiv⟩ :=
    local_time_uniform_corrected_derivative_normalized_cylinder d D.ellipticity
      D.one_le_ellipticity
  obtain ⟨_, _, hsource⟩ := local_time_corrected_cylinder_of_source_dependency h0 d hd D
  refine ⟨C₀, hC₀, ?_⟩
  intro p hp
  obtain ⟨Cp, hCp, hsource⟩ := hsource p hp
  refine ⟨Cp, hCp, ?_⟩
  intro Q hQ ζ P hP f hf t ht u w
  obtain ⟨hu₈, _, _, U, hU, heU, hUmoment⟩ := hsource Q hQ ζ P hP f hf t ht
  refine ⟨hu₈, ?_⟩
  obtain ⟨g, hregular, hmass⟩ := hderiv hP f ht
    (a := (t : ℝ) / 16) (b := (t : ℝ) / 8) (by positivity) (by linarith)
    U hU.measurable heU
  refine ⟨P ((t : ℝ) - (t : ℝ) / 16).toNNReal g,
    (hregular t (by linarith)).1, ?_⟩
  intro ρ z hρ
  have hρpos : 0 < ρ := (Real.sqrt_pos.mpr ht).trans_le hρ
  let N := fun ω : FieldPair d => Real.sqrt
    (⨍ s in Icc ((t : ℝ) / 4) (t : ℝ),
      ⨍ x in {x | euclideanNorm (x - z) < 8 * ρ}, ‖U (s, translate x ω)‖ ^ 2)
  have hNsq : ∀ ω, N ω ^ 2 =
      ⨍ s in Icc ((t : ℝ) / 4) (t : ℝ),
        ⨍ x in {x | euclideanNorm (x - z) < 8 * ρ}, ‖U (s, translate x ω)‖ ^ 2 := by
    intro ω
    exact Real.sq_sqrt (average_nonneg fun _ => average_nonneg fun _ => sq_nonneg _)
  have hN := hUmoment z (8 * ρ) (by positivity)
  have hbound : ∀ᵐ ω ∂reducedLaw Q,
      (t : ℝ) * (⨍ x in {x | euclideanNorm (x - z) < ρ},
        ‖(P ((t : ℝ) - (t : ℝ) / 16).toNNReal g) (translate x ω)‖ ^ 2) ≤
        (C₀ * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ 6 / (t : ℝ)) * N ω ^ 2 := by
    simpa only [hNsq] using hmass (by linarith) z ρ hρ
  obtain ⟨hmem, hnorm⟩ := local_time_zero_gradient_moment_of_sq_bound
    Q t ρ hρpos z (P ((t : ℝ) - (t : ℝ) / 16).toNNReal g)
    hN.1 (ae_of_all _ fun _ => Real.sqrt_nonneg _) (by positivity) hbound
  exact ⟨hmem, hnorm.trans (mul_le_mul le_rfl hN.2 zero_le zero_le)⟩

/- SUPERVISOR EXACT TARGET (not a declaration or proof); replace with proved command.
theorem local_time_derivative_moment_of_deps
  (h0 : EinsteinFull.Blueprint.node_l_u3A_forced_u2D_local_u23_centered_u2D_sourceStmt)
  (h1 : EinsteinFull.Blueprint.node_e_u3A_lp_u2D_growthStmt) :
∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∀ p : ℝ, 2 ≤ p → ∃ C Cp : ℝ, 1 ≤ C ∧ 0 < Cp ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
    ∃ G : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
    ∃ V : ℝ≥0 → Lp ℂ 2 (reducedLaw Q),
    (∀ t : ℝ≥0, 0 < (t : ℝ) →
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (indexedEndpoint hd Q ν ζ P Pdag β a μ t) (G t) ∧
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (uncenteredEndpoint hd Q ν ζ P Pdag β a μ t) (G t) ∧
      HasDerivAt (fun r : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ r.toNNReal)
        (V t) (t : ℝ)) ∧
    (∀ (t : ℝ≥0) (ht : 0 < (t : ℝ)),
      let U := indexedEndpoint hd Q ν ζ P Pdag β a μ t
      let U₈ := indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8)
      MemLp (U₈ : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
      (∀ (ρ : ℝ) (x : Vec d) (hρ : Real.sqrt (t : ℝ) ≤ ρ),
        MemLp (localSpatialEnergy Q t ρ (lt_of_lt_of_le (Real.sqrt_pos.mpr ht) hρ) x (0) (V t)) (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm (localSpatialEnergy Q t ρ (lt_of_lt_of_le (Real.sqrt_pos.mpr ht) hρ) x (0) (V t))
          (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        C * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C * (t : ℝ) ^ (-(1 / 2 : ℝ)) *
          Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
          (eLpNorm (U₈ : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal))
-/
end EinsteinFull.Blueprint
