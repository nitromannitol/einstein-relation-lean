import EinsteinFull.Blueprint.G2.node_e_u3A_energy_u2D_target
import EinsteinFull.Blueprint.Roots.node_p_u3A_scalar
import EinsteinFull.Blueprint.Foundation.node_e_u3A_centered_u2D_equations
import EinsteinFull.Blueprint.Foundation.node_stationary_u2D_environment
import EinsteinFull.Calculus.ComplexSemigroupCenteringSupport
import EinsteinFull.Calculus.ComplexCenteringSourceSupport
import EinsteinFull.Work.W3.ForwardLocalSpacetimeEnergySupport
import EinsteinFull.Work.W2.TransposeAllDataHorizonEnergySupport
import EinsteinFull.Blueprint.G3.Proofs.W3Queue0400_1
import EinsteinFull.Calculus.ComplexForcedGradientSupport
import EinsteinFull.Calculus.LocalEnergyDomainSupport

open MeasureTheory
open scoped NNReal ENNReal BigOperators

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- The scalar dependency controls exactly the sum of endpoint L2 norms
needed to restart stationary energy. The unused clock term is nonnegative. -/
theorem energyTarget_scalar_norms (hscalar : node_p_u3A_scalarStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
      (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ (ζ : ℂ)
      (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag →
      ∀ t : ℝ≥0, 1 ≤ (t : ℝ) → ‖ζ‖ * Real.sqrt (t : ℝ) ≤ 2 →
        ‖indexedEndpoint hd Q (Sum.inr true) ζ P Pdag β a μ t‖ +
          (∑ j : Fin d, ‖indexedEndpoint hd Q (Sum.inl j) ζ P Pdag β a μ t‖) ≤
            C * (t : ℝ) ^ (-(1 / 2 + (d : ℝ) / 4)) := by
  obtain ⟨a₀, η₀, _, _, _, hp⟩ := hscalar d hd D
  obtain ⟨C, Dp, t₀, Cder, hC, _, _, _, h⟩ := hp 2 le_rfl
  refine ⟨C, hC, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag t ht hζ
  have hb := (h Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag).1 t ht hζ
  have hp2 : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  simp only [hp2, ← Lp.norm_def] at hb
  change ‖transposeEndpoint Q ⟨0, by omega⟩ Pdag β t‖ +
    (∑ j : Fin d, ‖velocityEndpoint Q ⟨0, by omega⟩ j ζ P β a t‖) ≤ _
  exact (le_add_of_nonneg_right (norm_nonneg (clockEndpoint Q ζ P μ t))).trans hb.2

variable {d : ℕ} {Λ r : ℝ} {Q : EnvironmentLaw d Λ r}
  {ζ : ℂ} {P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}

/-- Restarting a centered velocity endpoint gives its literal later endpoint.
The center at the restart time is removed using constant preservation. -/
theorem energyTarget_velocity_restart (hd : 2 ≤ d)
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (j : Fin d) (s t : ℝ≥0) :
    centeredComplexLp Q (P s (velocityEndpoint Q ⟨0, by omega⟩ j ζ P β a t)) =
      velocityEndpoint Q ⟨0, by omega⟩ j ζ P β a (s + t) := by
  unfold velocityEndpoint
  rw [hP.centered_apply, hP.2.1]
  rfl

/-- The conservative transpose endpoint restarts by its actual transpose
semigroup, with the original signed complex force. -/
theorem energyTarget_transpose_restart (hd : 2 ≤ d)
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (s t : ℝ≥0) :
    Pdag s (transposeEndpoint Q ⟨0, by omega⟩ Pdag β t) =
      transposeEndpoint Q ⟨0, by omega⟩ Pdag β (s + t) := by
  unfold transposeEndpoint
  rw [hPdag.add hP]
  rfl

/-- Restarted velocity gradients are gradients of the actual later centered
endpoint; the assertion holds at every positive elapsed time. -/
theorem energyTarget_velocity_restarted_gradient (hd : 2 ≤ d)
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (j : Fin d) (t : ℝ≥0)
    {s : ℝ} (hs : 0 < s) :
    HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (velocityEndpoint Q ⟨0, by omega⟩ j ζ P β a (s.toNNReal + t))
      (hP.gradientOrbit (velocityEndpoint Q ⟨0, by omega⟩ j ζ P β a t) s) := by
  have h := hP.centered_gradientOrbit_spec
    (velocityEndpoint Q ⟨0, by omega⟩ j ζ P β a t) hs
  rwa [energyTarget_velocity_restart hd hP β a j s.toNNReal t] at h

/-- The actual restarted velocity gradient has integrable squared Euclidean
norm, controlled by the norm of the centered endpoint at the restart time. -/
theorem energyTarget_velocity_restarted_energy (hd : 2 ≤ d)
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (j : Fin d) (t : ℝ≥0)
    {T : ℝ} (hT : 0 ≤ T) :
    IntegrableOn (fun s =>
      ‖hP.gradientOrbit (velocityEndpoint Q ⟨0, by omega⟩ j ζ P β a t) s‖ ^ 2)
      (Set.Icc 0 T) ∧
    (∫ s in Set.Icc 0 T,
      ‖hP.gradientOrbit (velocityEndpoint Q ⟨0, by omega⟩ j ζ P β a t) s‖ ^ 2) ≤
        2 * (Real.exp (2 * Λ) * Λ) * Real.exp (2 * complexForceShift d Λ ζ * T) *
          ‖velocityEndpoint Q ⟨0, by omega⟩ j ζ P β a t‖ ^ 2 :=
  hP.integrableOn_Icc_sq_gradientOrbit_fullHorizon _ hT

/-- The actual conservative transpose restart has full-horizon energy. It
does not require generator-domain membership at the restart time. -/
theorem energyTarget_transpose_restarted_energy (hd : 2 ≤ d)
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0)
    {T : ℝ} (hT : 0 ≤ T) :
    IntegrableOn (fun s =>
      ‖complexTransposeGradientOrbit Q Pdag
        (transposeEndpoint Q ⟨0, by omega⟩ Pdag β t) s‖ ^ 2) (Set.Icc 0 T) ∧
    (∫ s in Set.Icc 0 T,
      ‖complexTransposeGradientOrbit Q Pdag
        (transposeEndpoint Q ⟨0, by omega⟩ Pdag β t) s‖ ^ 2) ≤
        2 * (Real.exp (2 * Λ) * Λ) * Real.exp (2 * complexForceShift d Λ ζ * T) *
          ‖transposeEndpoint Q ⟨0, by omega⟩ Pdag β t‖ ^ 2 :=
  hPdag.integrableOn_Icc_sq_gradientOrbit hP _ hT

/-- The force window in the source bounds the quadratic force-time product. -/
theorem energyTarget_force_time {ζ : ℂ} {t : ℝ} (ht : 0 ≤ t)
    (hζ : ‖ζ‖ * Real.sqrt (2 * t) ≤ 2) : ‖ζ‖ ^ 2 * t ≤ 2 := by
  have hs := mul_self_le_mul_self (by positivity : 0 ≤ ‖ζ‖ * Real.sqrt (2 * t)) hζ
  have he := Real.sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ht)
  nlinarith only [hs, he]


/-- A single continuous gradient family for the velocity and true transpose
endpoints, chosen on the closed half-line before any energy window. -/
theorem energyTarget_continuous_gradients
    (hd : 2 ≤ d) {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)}
    {a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)}
    (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (ha : IsReducedCoefficientObservation Q a)
    {P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag) :
    ∃ G : EndpointIndex d → ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ ν j, Continuous (fun t => G ν t j)) ∧
      ∀ ν, ν ≠ Sum.inr false → ∀ t,
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (indexedEndpoint hd Q ν ζ P Pdag β a μ t) (G ν t) := by
  classical
  choose Gf hGfc hGf using timeFlux_forward_continuous_gradient hβ ha hP
  obtain ⟨Gt, hGtc, hGt⟩ := timeFlux_transpose_continuous_gradient hβ hP hPdag
    ⟨0, by omega⟩
  let G : EndpointIndex d → ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q) := fun ν =>
    match ν with
    | .inl j => Gf j
    | .inr true => Gt
    | .inr false => fun _ _ => 0
  refine ⟨G, ?_, ?_⟩
  · rintro (j | b) l
    · exact hGfc j l
    · cases b
      · exact continuous_const
      · exact hGtc l
  · rintro (j | b) hν t
    · exact (hGf j t).centered
    · cases b
      · exact (hν rfl).elim
      · exact hGt t

/-- These same all-time gradients admit one jointly measurable representative
per endpoint and coordinate. Each fixed-time slice represents the selected
L2 class, with no time-exceptional set. -/
theorem energyTarget_joint_gradients
    (hd : 2 ≤ d) {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)}
    {a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)}
    (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (ha : IsReducedCoefficientObservation Q a)
    {P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag) :
    ∃ (G : EndpointIndex d → ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q))
      (g : EndpointIndex d → ℝ × FieldPair d → Fin d → ℂ),
      (∀ ν j, Continuous (fun t => G ν t j)) ∧
      (∀ ν j, Measurable (fun z => g ν z j)) ∧
      (∀ ν r j, (fun ω => g ν (r, ω) j) =ᵐ[reducedLaw Q] G ν r.toNNReal j) ∧
      ∀ ν, ν ≠ Sum.inr false → ∀ t,
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
          (indexedEndpoint hd Q ν ζ P Pdag β a μ t) (G ν t) := by
  classical
  letI := reducedLaw_probability Q
  obtain ⟨G, hGc, hG⟩ := energyTarget_continuous_gradients hd μ hβ ha hP hPdag
  have hm (ν : EndpointIndex d) (j : Fin d) :
      StronglyMeasurable (fun r : ℝ => G ν r.toNNReal j) :=
    ((hGc ν j).comp continuous_real_toNNReal).stronglyMeasurable
  choose g hgm hge using fun ν j => StronglyMeasurable.exists_joint_l2_representative (hm ν j)
  exact ⟨G, fun ν z j => g ν j z, hGc, hgm, (fun ν r j => hge ν j r), hG⟩


/-- Uniqueness identifies any selected actual later gradient with the
restarted energy orbit, coordinate by coordinate. -/
theorem energyTarget_velocity_selected_restart (hd : 2 ≤ d)
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (j : Fin d) (t : ℝ≥0)
    {s : ℝ} (hs : 0 < s) {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (velocityEndpoint Q ⟨0, by omega⟩ j ζ P β a (s.toNNReal + t)) G) :
    WithLp.toLp 2 G =
      hP.gradientOrbit (velocityEndpoint Q ⟨0, by omega⟩ j ζ P β a t) s := by
  exact WithLp.ofLp_injective 2
    (hG.unique (energyTarget_velocity_restarted_gradient hd hP β a j t hs))

/-- The true transpose restart uses the same gradient as the selected actual
later endpoint; its only time restriction is positive elapsed time. -/
theorem energyTarget_transpose_selected_restart (hd : 2 ≤ d)
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0)
    {s : ℝ} (hs : 0 < s) {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (transposeEndpoint Q ⟨0, by omega⟩ Pdag β (s.toNNReal + t)) G) :
    WithLp.toLp 2 G = complexTransposeGradientOrbit Q Pdag
      (transposeEndpoint Q ⟨0, by omega⟩ Pdag β t) s := by
  symm
  apply complexTransposeGradientOrbit_eq hs
  rwa [energyTarget_transpose_restart hd hP hPdag β s.toNNReal t]

/-- Every selected all-time endpoint gradient obeys the restarted total energy
bound. Equality is needed only at positive elapsed times, so no endpoint
convention in the general all-L2 energy orbit affects the integral. -/
theorem energyTarget_selected_restarted_energy (hd : 2 ≤ d)
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (G : EndpointIndex d → ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q))
    (hG : ∀ ν, ν ≠ Sum.inr false → ∀ r,
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (indexedEndpoint hd Q ν ζ P Pdag β a μ r) (G ν r))
    (ν : EndpointIndex d) (hν : ν ≠ Sum.inr false) (t : ℝ≥0)
    {T : ℝ} (hT : 0 ≤ T) :
    IntegrableOn (fun s => ‖WithLp.toLp 2 (G ν (s.toNNReal + t))‖ ^ 2)
      (Set.Icc 0 T) ∧
    (∫ s in Set.Icc 0 T, ‖WithLp.toLp 2 (G ν (s.toNNReal + t))‖ ^ 2) ≤
      2 * (Real.exp (2 * Λ) * Λ) * Real.exp (2 * complexForceShift d Λ ζ * T) *
        ‖indexedEndpoint hd Q ν ζ P Pdag β a μ t‖ ^ 2 := by
  have transfer (F H : ℝ → ℝ) (he : ∀ s, 0 < s → F s = H s)
      (hi : IntegrableOn H (Set.Icc 0 T)) :
      IntegrableOn F (Set.Icc 0 T) ∧
        (∫ s in Set.Icc 0 T, F s) = ∫ s in Set.Icc 0 T, H s := by
    have hae : F =ᵐ[volume.restrict (Set.Ioc 0 T)] H := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact he s hs.1
    constructor
    · rw [integrableOn_Icc_iff_integrableOn_Ioc] at hi ⊢
      exact hi.congr hae.symm
    · rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc]
      exact integral_congr_ae hae
  rcases ν with j | b
  · obtain ⟨hi, hb⟩ := energyTarget_velocity_restarted_energy hd hP β a j t hT
    obtain ⟨hi', he⟩ := transfer _ _ (fun s hs => congrArg (fun x => ‖x‖ ^ 2)
      (energyTarget_velocity_selected_restart hd hP β a j t hs
        (hG (Sum.inl j) (by simp) _))) hi
    exact ⟨hi', he.trans_le hb⟩
  · cases b
    · exact (hν rfl).elim
    · obtain ⟨hi, hb⟩ := energyTarget_transpose_restarted_energy hd hP hPdag β t hT
      obtain ⟨hi', he⟩ := transfer _ _ (fun s hs => congrArg (fun x => ‖x‖ ^ 2)
        (energyTarget_transpose_selected_restart hd hP hPdag β t hs
          (hG (Sum.inr true) (by simp) _))) hi
      exact ⟨hi', he.trans_le hb⟩


/-- Translating the elapsed-time energy gives the precise closed source
window [t,2t] for the common selected gradient family. -/
theorem energyTarget_selected_window_energy (hd : 2 ≤ d)
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (G : EndpointIndex d → ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q))
    (hGc : ∀ ν j, Continuous (fun r => G ν r j))
    (hG : ∀ ν, ν ≠ Sum.inr false → ∀ r,
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (indexedEndpoint hd Q ν ζ P Pdag β a μ r) (G ν r))
    (ν : EndpointIndex d) (hν : ν ≠ Sum.inr false) (t : ℝ≥0) :
    IntegrableOn (fun r : ℝ => ‖WithLp.toLp 2 (G ν r.toNNReal)‖ ^ 2)
      (Set.Icc (t : ℝ) (2 * t)) ∧
    (∫ r in Set.Icc (t : ℝ) (2 * t), ‖WithLp.toLp 2 (G ν r.toNNReal)‖ ^ 2) ≤
      2 * (Real.exp (2 * Λ) * Λ) * Real.exp (2 * complexForceShift d Λ ζ * t) *
        ‖indexedEndpoint hd Q ν ζ P Pdag β a μ t‖ ^ 2 := by
  let F : ℝ → ℝ := fun r => ‖WithLp.toLp 2 (G ν r.toNNReal)‖ ^ 2
  have hc : Continuous F :=
    (((PiLp.continuous_toLp 2 _).comp (continuous_pi (hGc ν))).comp
      continuous_real_toNNReal).norm.pow 2
  refine ⟨hc.continuousOn.integrableOn_Icc, ?_⟩
  have hb := (energyTarget_selected_restarted_energy hd hP hPdag β a μ G hG ν hν t
    t.property).2
  have he (s : ℝ) (hs : s ∈ Set.uIcc (0 : ℝ) (t : ℝ)) :
      F (s + t) = ‖WithLp.toLp 2 (G ν (s.toNNReal + t))‖ ^ 2 := by
    rw [Set.uIcc_of_le (show (0 : ℝ) ≤ (t : ℝ) from t.property)] at hs
    dsimp only [F]
    have heN : (s + (t : ℝ)).toNNReal = s.toNNReal + t := by
      calc
        _ = s.toNNReal + (t : ℝ).toNNReal :=
          Real.toNNReal_add (r := s) (p := (t : ℝ)) hs.1 t.property
        _ = _ := by rw [Real.toNNReal_coe]
    exact congrArg (fun r => ‖WithLp.toLp 2 (G ν r)‖ ^ 2) heN
  have he' := intervalIntegral.integral_congr (μ := volume) he
  rw [intervalIntegral.integral_comp_add_right] at he'
  simp only [zero_add] at he'
  rw [intervalIntegral.integral_of_le (μ := volume) (a := (0 : ℝ)) (b := (t : ℝ)) t.property,
    intervalIntegral.integral_of_le (μ := volume) (a := (t : ℝ)) (b := (t : ℝ) + t)
      (le_add_of_nonneg_right (show (0 : ℝ) ≤ (t : ℝ) from t.property)),
    ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc] at he'
  have h2 : (t : ℝ) + t = 2 * t := by ring
  rw [h2] at he'
  exact he'.trans_le hb


/-- The common joint representative has the literal environment energy on
[t,2t], equal to the Euclidean selected-gradient norm. In particular the time
integrability required by the source target follows without a new premise. -/
theorem energyTarget_joint_window_energy (hd : 2 ≤ d)
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (G : EndpointIndex d → ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q))
    (g : EndpointIndex d → ℝ × FieldPair d → Fin d → ℂ)
    (hGc : ∀ ν j, Continuous (fun r => G ν r j))
    (hge : ∀ ν r j, (fun ω => g ν (r, ω) j) =ᵐ[reducedLaw Q] G ν r.toNNReal j)
    (hG : ∀ ν, ν ≠ Sum.inr false → ∀ r,
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (indexedEndpoint hd Q ν ζ P Pdag β a μ r) (G ν r))
    (ν : EndpointIndex d) (hν : ν ≠ Sum.inr false) (t : ℝ≥0) :
    IntegrableOn (fun r : ℝ => ∫ ω, ∑ j, ‖g ν (r, ω) j‖ ^ 2 ∂reducedLaw Q)
      (Set.Icc (t : ℝ) (2 * t)) ∧
    (∫ r in Set.Icc (t : ℝ) (2 * t), ∫ ω, ∑ j, ‖g ν (r, ω) j‖ ^ 2 ∂reducedLaw Q) ≤
      2 * (Real.exp (2 * Λ) * Λ) * Real.exp (2 * complexForceShift d Λ ζ * t) *
        ‖indexedEndpoint hd Q ν ζ P Pdag β a μ t‖ ^ 2 := by
  have he (r : ℝ) : (∫ ω, ∑ j, ‖g ν (r, ω) j‖ ^ 2 ∂reducedLaw Q) =
      ‖WithLp.toLp 2 (G ν r.toNNReal)‖ ^ 2 :=
    (integral_jointForwardGradientEnergy (G := fun r => WithLp.toLp 2 (G ν r.toNNReal))
      (V := fun j z => g ν z j) (fun j r => hge ν r j) r).2
  simpa only [he] using
    energyTarget_selected_window_energy hd hP hPdag β a μ G hGc hG ν hν t


/-- The exact bounded-force window removes force and time from the growth
factor in the stationary energy estimate. -/
theorem energyTarget_uniform_force_exponential {Λ : ℝ} (hΛ : 0 ≤ Λ)
    {t : ℝ} (ht : 0 ≤ t) {ζ : ℂ}
    (hζ : ‖ζ‖ * Real.sqrt (2 * t) ≤ 2) :
    Real.exp (2 * complexForceShift d Λ ζ * t) ≤
      Real.exp (4 * (Real.exp (2 * Λ) * Λ) *
        ((d : ℝ) * (Real.exp (2 * Λ) * Λ)) ^ 2) := by
  have hforce := energyTarget_force_time ht hζ
  let K := Real.exp (2 * Λ) * Λ
  have hK : 0 ≤ K := mul_nonneg (Real.exp_pos _).le hΛ
  apply Real.exp_le_exp.mpr
  change 2 * (K * (‖ζ‖ * ((d : ℝ) * K)) ^ 2) * t ≤ _
  calc
    2 * (K * (‖ζ‖ * ((d : ℝ) * K)) ^ 2) * t =
        (2 * K * ((d : ℝ) * K) ^ 2) * (‖ζ‖ ^ 2 * t) := by ring
    _ ≤ (2 * K * ((d : ℝ) * K) ^ 2) * 2 :=
      mul_le_mul_of_nonneg_left hforce (by positivity)
    _ = _ := by dsimp only [K]; ring


/-- Stationary Fubini cancels the exact spatial normalization. The time
measure is arbitrary, so this applies to the closed source window. -/
theorem energyTarget_normalized_average
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {ν : Measure ℝ} [SFinite ν] (B : Set (Vec d))
    [IsFiniteMeasure (volume.restrict B)] (hB : 0 < volume.real B)
    {E : ℝ × FieldPair d → ℝ} (hE : Measurable E)
    (hi : Integrable E (ν.prod Q)) :
    Integrable (fun ω => ∫ s, (⨍ y in B, E (s, translate y ω)) ∂ν) Q ∧
    (∫ ω, ∫ s, (⨍ y in B, E (s, translate y ω)) ∂ν ∂Q) =
      ∫ s, (∫ ω, E (s, ω) ∂Q) ∂ν := by
  have ht := integrable_joint_spatial_energy Q hQ (volume.restrict B) hi
  have he : (fun ω => ∫ s, (∫ y in B, E (s, translate y ω)) ∂ν) =ᵐ[Q]
      (fun ω => ∫ p : Vec d × ℝ, E (p.2, translate p.1 ω)
        ∂((volume.restrict B).prod ν)) := by
    filter_upwards [ht.prod_left_ae] with ω hω
    exact (integral_prod_symm _ hω).symm
  have ha := ht.integral_prod_right.congr he.symm
  have hn (ω : FieldPair d) :
      (∫ s, (⨍ y in B, E (s, translate y ω)) ∂ν) =
        (volume.real B)⁻¹ * ∫ s, (∫ y in B, E (s, translate y ω)) ∂ν := by
    simp only [setAverage_eq, smul_eq_mul, integral_const_mul]
  constructor
  · simpa only [hn] using ha.const_mul (volume.real B)⁻¹
  · simp_rw [hn]
    rw [integral_const_mul, integral_congr_ae he,
      integral_joint_spatial_energy Q hQ _ hE hi]
    simp only [Measure.real, Measure.restrict_apply_univ]
    rw [← mul_assoc]
    change ((volume.real B)⁻¹ * volume.real B) * _ = _
    rw [inv_mul_cancel₀ hB.ne', one_mul]

/-- A nonnegative integrable energy has a square root in L2 with the exact
square-root expectation norm. -/
theorem energyTarget_sqrt_norm {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {A : Ω → ℝ} (hA : Integrable A μ) (hn : ∀ ω, 0 ≤ A ω) :
    MemLp (fun ω => Real.sqrt (A ω)) 2 μ ∧
      (eLpNorm (fun ω => Real.sqrt (A ω)) 2 μ).toReal = Real.sqrt (∫ ω, A ω ∂μ) := by
  have hs : AEStronglyMeasurable (fun ω => Real.sqrt (A ω)) μ :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hA.aestronglyMeasurable
  have he (ω : Ω) : ‖Real.sqrt (A ω)‖ ^ 2 = A ω := by
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (hn ω)]
  have hm : MemLp (fun ω => Real.sqrt (A ω)) 2 μ :=
    (memLp_two_iff_integrable_sq_norm hs).mpr (by simpa only [he] using hA)
  refine ⟨hm, ?_⟩
  have hsq : (eLpNorm (fun ω => Real.sqrt (A ω)) 2 μ).toReal ^ 2 = ∫ ω, A ω ∂μ := by
    rw [← Lp.norm_toLp _ hm, ← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hm.coeFn_toLp] with ω hω
    simp only [hω, real_inner_self_eq_norm_sq, he]
  rw [← hsq, Real.sqrt_sq ENNReal.toReal_nonneg]


/-- The normalized Euclidean local energy has exactly the stationary
Euclidean gradient energy as its squared L2 norm. -/
theorem energyTarget_local_window_norm
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {ν : Measure ℝ} [SFinite ν]
    {G : ℝ → PiLp 2 (fun _ : Fin d => Lp ℂ 2 Q)}
    {g : Fin d → ℝ × FieldPair d → ℂ} (hgm : ∀ j, Measurable (g j))
    (hge : ∀ j r, (fun ω => g j (r, ω)) =ᵐ[Q] G r j)
    (hi : Integrable (fun r => ‖G r‖ ^ 2) ν) :
    let E := fun ω => Real.sqrt (∫ r, (⨍ y in {y : Vec d | euclideanNorm y < 1},
      ∑ j, ‖g j (r, translate y ω)‖ ^ 2) ∂ν)
    MemLp E 2 Q ∧ (eLpNorm E 2 Q).toReal = Real.sqrt (∫ r, ‖G r‖ ^ 2 ∂ν) := by
  let B := {y : Vec d | euclideanNorm y < 1}
  have hB : 0 < volume.real B := by
    simpa only [sub_zero] using localSpatialEnergy_window_volume (0 : Vec d) 1 zero_lt_one
  letI : IsFiniteMeasure (volume.restrict B) :=
    isFiniteMeasure_restrict.mpr (ENNReal.toReal_pos_iff.mp hB).2.ne
  have hji := integrable_jointForwardGradientEnergy hgm hge hi
  obtain ⟨ha, he⟩ := energyTarget_normalized_average Q hQ B hB
    (measurable_jointForwardGradientEnergy hgm) hji
  have hn (ω : FieldPair d) :
      0 ≤ ∫ r, (⨍ y in B, jointForwardGradientEnergy g (r, translate y ω)) ∂ν := by
    apply integral_nonneg
    intro r
    apply integral_nonneg
    intro y
    exact Finset.sum_nonneg (fun j _ => sq_nonneg _)
  obtain ⟨hm, hnorm⟩ := energyTarget_sqrt_norm ha hn
  refine ⟨hm, ?_⟩
  apply hnorm.trans
  apply congrArg Real.sqrt
  exact he.trans (integral_congr_ae (ae_of_all _ fun r =>
    (integral_jointForwardGradientEnergy hge r).2))


/-- Exact graph reduction for the stationary energy target. The prescribed
centered-equation and stationary-environment Props are retained in graph order;
the adopted actual gradient and stationary Fubini APIs already prove the
parts of those dependencies needed in this energy argument. -/
@[nolint unusedArguments]
theorem node_e_u3A_energy_u2D_target_of_deps
    (hscalar : node_p_u3A_scalarStmt)
    (_hcentered : node_e_u3A_centered_u2D_equationsStmt)
    (_hstationary : node_stationary_u2D_environmentStmt) :
    node_e_u3A_energy_u2D_targetStmt := by
  intro d hd D
  obtain ⟨C, hC, hscalarNorm⟩ := energyTarget_scalar_norms hscalar d hd D
  let K := Real.exp (2 * D.ellipticity) * D.ellipticity
  have hK : 0 < K := mul_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one D.one_le_ellipticity)
  let R := Real.sqrt (2 * K * Real.exp (4 * K * ((d : ℝ) * K) ^ 2))
  have hR : 0 < R := Real.sqrt_pos.mpr (by positivity)
  refine ⟨R * C, mul_pos hR hC, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag
  letI := reducedLaw_probability Q
  obtain ⟨G, g, hGc, hgm, hge, hG⟩ := energyTarget_joint_gradients hd μ hβ ha hP hPdag
  refine ⟨G, g, (fun ν _ j => (hgm ν j).aestronglyMeasurable), ?_, ?_, ?_⟩
  · intro ν _ r _ j
    simpa only [Real.toNNReal_coe] using hge ν (r : ℝ) j
  · intro ν hν r _
    exact hG ν hν r
  · intro t ht hζ
    let tn : ℝ≥0 := ⟨t, by linarith⟩
    let E : EndpointIndex d → FieldPair d → ℝ := fun ν ω =>
      Real.sqrt (∫ r in Set.Icc t (2 * t),
        ⨍ y in {y : Vec d | euclideanNorm y < 1},
          ∑ j : Fin d, ‖g ν (r, translate y ω) j‖ ^ 2)
    have hnorm (ν : EndpointIndex d) (hν : ν ≠ Sum.inr false) :
        MemLp (E ν) 2 (reducedLaw Q) ∧
        (eLpNorm (E ν) 2 (reducedLaw Q)).toReal =
          Real.sqrt (∫ r in Set.Icc t (2 * t),
            ‖WithLp.toLp 2 (G ν r.toNNReal)‖ ^ 2) :=
      energyTarget_local_window_norm (reducedLaw Q) (reducedLaw_stationary Q)
        (G := fun r => WithLp.toLp 2 (G ν r.toNNReal))
        (g := fun j z => g ν z j) (hgm ν) (fun j r => hge ν r j)
        (energyTarget_selected_window_energy hd hP hPdag β a μ G hGc hG ν hν tn).1
    have hb (ν : EndpointIndex d) (hν : ν ≠ Sum.inr false) :
        (eLpNorm (E ν) 2 (reducedLaw Q)).toReal ≤
          R * ‖indexedEndpoint hd Q ν ζ P Pdag β a μ tn‖ := by
      rw [(hnorm ν hν).2]
      have he := energyTarget_uniform_force_exponential
        (zero_le_one.trans D.one_le_ellipticity) (by linarith : 0 ≤ t) hζ (d := d)
      have hh := (energyTarget_selected_window_energy hd hP hPdag β a μ G hGc hG ν hν tn).2
      have hbound : (∫ r in Set.Icc t (2 * t), ‖WithLp.toLp 2 (G ν r.toNNReal)‖ ^ 2) ≤
          (2 * K * Real.exp (4 * K * ((d : ℝ) * K) ^ 2)) *
            ‖indexedEndpoint hd Q ν ζ P Pdag β a μ tn‖ ^ 2 :=
        hh.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 2 * K)) (sq_nonneg _))
      apply (Real.sqrt_le_sqrt hbound).trans_eq
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]
    change (∀ ν, ν ≠ Sum.inr false →
      IntegrableOn (fun r : ℝ => ∫ ω, ∑ j, ‖g ν (r, ω) j‖ ^ 2 ∂reducedLaw Q)
        (Set.Icc t (2 * t)) ∧ MemLp (E ν) 2 (reducedLaw Q)) ∧ _
    constructor
    · intro ν hν
      exact ⟨(energyTarget_joint_window_energy hd hP hPdag β a μ G g hGc hge hG ν hν tn).1,
        (hnorm ν hν).1⟩
    · calc
        (eLpNorm (E (Sum.inr true)) 2 (reducedLaw Q)).toReal +
            ∑ j, (eLpNorm (E (Sum.inl j)) 2 (reducedLaw Q)).toReal ≤
            R * ‖indexedEndpoint hd Q (Sum.inr true) ζ P Pdag β a μ tn‖ +
              ∑ j, R * ‖indexedEndpoint hd Q (Sum.inl j) ζ P Pdag β a μ tn‖ :=
          add_le_add (hb _ (by simp)) (Finset.sum_le_sum fun j _ => hb _ (by simp))
        _ = R * (‖indexedEndpoint hd Q (Sum.inr true) ζ P Pdag β a μ tn‖ +
            ∑ j, ‖indexedEndpoint hd Q (Sum.inl j) ζ P Pdag β a μ tn‖) := by
          rw [← Finset.mul_sum, mul_add]
        _ ≤ R * (C * t ^ (-(1 / 2 + (d : ℝ) / 4))) :=
          mul_le_mul_of_nonneg_left
            (hscalarNorm Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag tn ht
              ((mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith : t ≤ 2 * t))
                (norm_nonneg ζ)).trans hζ)) hR.le
        _ = (R * C) * t ^ (-(1 / 2 + (d : ℝ) / 4)) := by ring

end EinsteinFull.Blueprint
