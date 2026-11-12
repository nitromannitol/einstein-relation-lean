import EinsteinRelation.Correctors.P53SourceSkewHeatTransport
import EinsteinRelation.Correctors.P53SourceSkewStationaryRepresentative
import EinsteinRelation.Correctors.P53SourceSkewHeatSelectionAlgebra
import EinsteinRelation.Correctors.SpatialWeakCongruence
import EinsteinRelation.Correctors.WeakPartialAddition
import EinsteinRelation.Correctors.AKMCorrectorScaling

/-!
# The stationary heat-selected flux-corrector gradient

Source: `paper/main.tex:732-748`; AKM (6.7) and Lemma 6.1. The physical
heat-selected gradient is covariant under translations, because the literal heat
formula commutes with them and selects a unique local `L²` limit. It is therefore
the orbit of one square-integrable stationary field `F`. Antisymmetrizing the
potential gives a skew field at every point with the same selected gradient, and
the cyclic sums of `F` vanish along almost every orbit.
-/

open MeasureTheory Filter Topology
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM HeatSelectedSkewMeaning

/-- The centered canonical flux along the orbit of a reduced pair. -/
def centeredFluxOrbit {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (ρ : FieldPair d) (y : Vec d) : Vec d :=
  (canonicalCorrectorFlux Q i (translate y ρ) - expectedCorrectorFlux Q i).ofLp

theorem centeredFluxOrbit_translate {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
    (i : Fin d) (ρ : FieldPair d) (z : Vec d) :
    centeredFluxOrbit Q i (translate z ρ) = fun x => centeredFluxOrbit Q i ρ (x + z) := by
  funext x
  simp only [centeredFluxOrbit, translate_add]

/-- The skew symmetrization of a matrix field. -/
def skewPart {d : ℕ} (σ : FieldPair d → Vec d → Mat d) (ρ : FieldPair d) (x : Vec d) :
    Mat d :=
  fun j k => (σ ρ x j k - σ ρ x k j) / 2

theorem skewPart_transpose {d : ℕ} (σ : FieldPair d → Vec d → Mat d) (ρ : FieldPair d)
    (x : Vec d) : (skewPart σ ρ x).transpose = -(skewPart σ ρ x) := by
  ext j k
  simp only [Matrix.transpose_apply, Matrix.neg_apply, skewPart]
  ring

/-- AKM (6.7) has a square-integrable stationary gradient field `F`, whose orbits
are the weak gradients of a jointly measurable, pointwise skew potential and are
selected by the literal heat formula. The orbits are antisymmetric and closed.
Inputs: `FluxGradientEstimate` (AKM Lemma 6.1) and `BallPoincareEstimate`. -/
theorem exists_stationary_heatSelected_skew_potential (h68 : FluxGradientEstimate)
    (hP : External.GilbargTrudinger.BallPoincareEstimate)
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    ∃ (σ : FieldPair d → Vec d → Mat d) (F : FieldPair d → Fin d → Fin d → Fin d → ℝ),
      (∀ j k, Measurable (fun p : FieldPair d × Vec d => σ p.1 p.2 j k)) ∧
      (∀ ρ x, (σ ρ x).transpose = -(σ ρ x)) ∧
      (∀ j k l, Measurable (fun ρ => F ρ j k l)) ∧
      (∀ j k l, MemLp (fun ρ => F ρ j k l) 2 (reducedEnvironmentLaw Q)) ∧
      ∀ᵐ ρ ∂reducedEnvironmentLaw Q,
        IsHeatSelectedFluxGradient (centeredFluxOrbit Q i ρ)
          (fun j k x l => F (translate x ρ) j k l) ∧
        (∀ j k, HasWeakGradient Set.univ (fun x => σ ρ x j k)
          (fun x l => F (translate x ρ) j k l)) ∧
        (∀ R : ℝ, 0 < R → ∀ j k,
          MemLp (fun x => σ ρ x j k) 2 (volume.restrict (ball 0 R))) ∧
        (∀ j k l, ∀ᵐ x ∂(volume : Measure (Vec d)),
          F (translate x ρ) k j l = -F (translate x ρ) j k l) ∧
        (∀ j k l, ∀ᵐ x ∂(volume : Measure (Vec d)),
          F (translate x ρ) j k l + F (translate x ρ) k l j + F (translate x ρ) l j k = 0) := by
  obtain ⟨σ₀, G, hσm, hGm, hae, hmom⟩ := exists_physical_heatSelected_fluxGradient h68 hP Q i
  set Qr := reducedEnvironmentLaw Q with hQrdef
  have hQr : IsStationary Qr := reducedEnvironmentLaw_stationary Q
  have hd : 0 < d := by have := (Fact.out : 2 ≤ d); omega
  -- covariance of the selected gradient
  have hcov (j k l : Fin d) (z : Vec d) : ∀ᵐ ρ ∂Qr, ∀ᵐ x ∂(volume : Measure (Vec d)),
      G (translate z ρ) j k x l = G ρ j k (x + z) l := by
    filter_upwards [hae, (measurePreserving_translate Qr hQr z).quasiMeasurePreserving.ae hae]
      with ρ hρ hzρ
    have hsel : IsHeatSelectedFluxGradient (fun x => centeredFluxOrbit Q i ρ (x + z))
        (G (translate z ρ)) := by
      rw [← centeredFluxOrbit_translate]
      exact hzρ.1
    exact isHeatSelectedFluxGradient_ae_translate_eq hρ.1 z hsel j k l
  have hloc (j k l : Fin d) : ∀ᵐ ρ ∂Qr, LocallyIntegrable (fun x => G ρ j k x l) volume := by
    filter_upwards [hae] with ρ hρ
    exact locallyIntegrableOn_univ.mp ((hρ.2.1 j k) l).2.1
  let F : FieldPair d → Fin d → Fin d → Fin d → ℝ := fun ρ j k l =>
    stationaryRepresentative (fun ρ x => G ρ j k x l) ρ
  have horbit (j k l : Fin d) : ∀ᵐ ρ ∂Qr, ∀ᵐ x ∂(volume : Measure (Vec d)),
      F (translate x ρ) j k l = G ρ j k x l :=
    ae_orbit_stationaryRepresentative Qr (hGm j k l) (hloc j k l) (hcov j k l)
  have hFm (j k l : Fin d) : Measurable (fun ρ => F ρ j k l) :=
    measurable_stationaryRepresentative (hGm j k l)
  have horbitAll : ∀ᵐ ρ ∂Qr, ∀ j k l : Fin d, ∀ᵐ x ∂(volume : Measure (Vec d)),
      F (translate x ρ) j k l = G ρ j k x l :=
    ae_all_iff.mpr fun j => ae_all_iff.mpr fun k => ae_all_iff.mpr fun l => horbit j k l
  refine ⟨skewPart σ₀, F, ?_, skewPart_transpose σ₀, hFm, ?_, ?_⟩
  · intro j k
    exact ((hσm j k).sub (hσm k j)).div_const 2
  · intro j k l
    exact memLp_two_of_orbit_lintegral Qr hQr (hFm j k l) (horbit j k l) (hmom j k l)
  filter_upwards [hae, horbitAll] with ρ hρ hFρ
  obtain ⟨hsel, hweak, hL2⟩ := hρ
  have hselF : IsHeatSelectedFluxGradient (centeredFluxOrbit Q i ρ)
      (fun j k x l => F (translate x ρ) j k l) :=
    isHeatSelectedFluxGradient_congr_ae hsel fun j k l =>
      (hFρ j k l).mono fun x hx => hx.symm
  have hswap (j k l : Fin d) : ∀ᵐ x ∂(volume : Measure (Vec d)),
      F (translate x ρ) k j l = -F (translate x ρ) j k l :=
    isHeatSelectedFluxGradient_ae_swap hselF j k l
  refine ⟨hselF, ?_, ?_, hswap, isHeatSelectedFluxGradient_cyclic hselF⟩
  · intro j k
    have hGF (a b : Fin d) :
        (fun x => G ρ a b x) =ᵐ[volume] (fun x l => F (translate x ρ) a b l) := by
      filter_upwards [ae_all_iff.mpr (fun l => hFρ a b l)] with x hx
      funext l
      exact (hx l).symm
    intro l
    have h1 := hasWeakGradient_const_mul (hweak j k) (1 / 2) l
    have h2 := hasWeakGradient_const_mul (hweak k j) (-(1 / 2)) l
    have hsum := hasWeakPartialDerivative_add h1 h2
    refine hasWeakPartialDerivative_congr_ae isOpen_univ hsum ?_ ?_
    · exact ae_of_all _ fun x => by simp only [skewPart]; ring
    · rw [Measure.restrict_univ]
      filter_upwards [hGF j k, hGF k j, hswap j k l] with x hxjk hxkj hx
      simp only [Pi.smul_apply, smul_eq_mul, hxjk, hxkj, hx]
      ring
  · intro R hR j k
    refine (((hL2 R hR j k).sub (hL2 R hR k j)).const_mul (1 / 2)).ae_eq
      (ae_of_all _ fun x => ?_)
    simp only [skewPart, Pi.sub_apply]
    ring

end EinsteinRelation.Correctors
