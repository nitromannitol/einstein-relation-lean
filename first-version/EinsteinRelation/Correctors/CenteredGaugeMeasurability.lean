import EinsteinRelation.Correctors.ConditionalCenteredMeasurability
import EinsteinRelation.Correctors.RegularRepresentativeSelection

/-! Source: `paper/main.tex:770-786,886-894`. Measurable shrinking
averages recover continuous gauge representatives. Centering then removes
the gauge constants, including when the original measurable potential
has arbitrary point values on spatial null sets. -/

open MeasureTheory
namespace EinsteinRelation.Correctors
open NormalizedSpatialRepresentativeSupport

/-- Shrinking averages recover a continuous gauge representative.
Source: `paper/main.tex:770-772,886-894`. -/
theorem spatialRegularRepresentative_eq_add_const {d : ℕ}
    (f g : Vec d → ℝ) (c : ℝ) (hg : Continuous g)
    (he : f =ᵐ[volume] fun x => g x + c) :
    spatialRegularRepresentative (fun _ : Unit => f) () = fun x => g x + c := by
  ext x
  refine spatialRegularRepresentative_eq_of_continuousOn_ae f (fun x => g x + c) Set.univ
    isOpen_univ (hg.add continuous_const).continuousOn ?_ x (Set.mem_univ x)
  simpa only [Measure.restrict_univ] using he

/-- Continuous gauges have identical centered scalar observables.
Source: `paper/main.tex:770-772,886-894`. -/
theorem centered_scalar_eq_of_continuous_gauge {d : ℕ}
    (ζ : SourceMollifier d) (R : ℝ) (hR : 1 ≤ R) (y : Point d)
    (f g : Point d → ℝ) (hf : Continuous f) (hg : Continuous g)
    (he : ∃ c : ℝ, f =ᵐ[volume] fun x => g x + c) :
    f y - (∫ x, sourceScaledMollifierKernel ζ R y x * f x) =
      g y - (∫ x, sourceScaledMollifierKernel ζ R y x * g x) := by
  let F : SpatialPotential d ℝ := ⟨f, hf.locallyIntegrable⟩
  let G : SpatialPotential d ℝ := ⟨g, hg.locallyIntegrable⟩
  exact sourceMollifierCenteredRepresentative_pointwise_independent ζ R hR y F G he hf hg y

/-- A jointly measurable gauge class has a.e. measurable centered point
observables for every supplied a.e. continuous representative.
Source: `paper/main.tex:770-786,886-894`. -/
theorem aestronglyMeasurable_centered_skew_of_measurable_gauge {d : ℕ}
    (μ : Measure (FieldPair d)) (ζ : SourceMollifier d) (R : ℝ) (hR : 1 ≤ R)
    (y : Point d) (σ τ : FieldPair d → Vec d → Mat d)
    (hτ : ∀ j k, Measurable (fun p : FieldPair d × Vec d => τ p.1 p.2 j k))
    (hσ : ∀ᵐ ω ∂μ, Continuous (σ ω))
    (he : ∀ᵐ ω ∂μ, ∀ j k, ∃ c : ℝ,
      (fun x => τ ω x j k) =ᵐ[volume] fun x => σ ω x j k + c) :
    AEStronglyMeasurable (conditionalCenteredSkew ζ R y σ) μ := by
  letI : TopologicalSpace.PseudoMetrizableSpace (Mat d) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin d → Fin d → ℝ))
  letI : SecondCountableTopology (Mat d) :=
    inferInstanceAs (SecondCountableTopology (Fin d → Fin d → ℝ))
  let τr : FieldPair d → Vec d → Mat d := fun ω x j k =>
    spatialRegularRepresentative (fun ρ z => τ ρ z j k) ω x
  have hτrm (j k : Fin d) :
      Measurable (fun p : FieldPair d × Vec d => τr p.1 p.2 j k) := by
    have hflip : Measurable (fun p : Vec d × FieldPair d => τ p.2 p.1 j k) :=
      (hτ j k).comp measurable_swap
    have hm : Measurable (fun p : Vec d × FieldPair d =>
        spatialRegularRepresentative (fun (ρ : FieldPair d) (z : Vec d) => τ ρ z j k)
          p.2 p.1) :=
      measurable_spatialRegularRepresentative
        (fun (ρ : FieldPair d) (z : Vec d) => τ ρ z j k) hflip
    have hs : Measurable (Prod.swap : FieldPair d × Vec d → Vec d × FieldPair d) :=
      measurable_swap
    have ht := hm.comp hs
    exact ht
  have hcm := (measurable_conditionalCentered_of_joint ζ R y
    (fun _ _ => 0) τr measurable_const hτrm).2
  have hEq : conditionalCenteredSkew ζ R y τr =ᵐ[μ] conditionalCenteredSkew ζ R y σ := by
    filter_upwards [hσ, he] with ω hσω heω
    apply funext
    intro j
    apply funext
    intro k
    obtain ⟨c, hc⟩ := heω j k
    have hσc : Continuous (fun x => σ ω x j k) :=
      (continuous_apply k).comp ((continuous_apply j).comp hσω)
    have hrec : ∀ x, τr ω x j k = σ ω x j k + c :=
      congrFun (spatialRegularRepresentative_eq_add_const _ _ c hσc hc)
    have hgc : Continuous (fun x : Point d => σ ω x.ofLp j k) :=
      hσc.comp (PiLp.continuous_ofLp 2 (fun _ : Fin d => ℝ))
    have hfc : Continuous (fun x : Point d => τr ω x.ofLp j k) :=
      (hgc.add continuous_const).congr (fun x => (hrec x.ofLp).symm)
    exact centered_scalar_eq_of_continuous_gauge ζ R hR y _ _ hfc hgc
      ⟨c, ae_of_all _ (fun x => hrec x.ofLp)⟩
  exact hcm.aestronglyMeasurable.congr hEq

end EinsteinRelation.Correctors
