import EinsteinRelation.Correctors.StationarySpatialHorizontal
import EinsteinRelation.Correctors.CanonicalVariationalGradientSupport

/-! # Finite-time spatial potentials in the horizontal H¹ domain

Source: `paper/main.tex:808-816`. Square-integrable stationary spatial
potentials give actual strong translation-generator gradients, with the
same Euclidean L² representatives used by the canonical corrector.
-/
open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors

/-- A stationary spatial weak potential realizes its given L² gradient in H¹. -/
theorem exists_horizontalH1_of_stationary_spatial_potential {d : ℕ}
    (μ : Measure (FieldPair d)) [IsProbabilityMeasure μ] (hμ : IsStationary μ)
    (f : Lp ℝ 2 μ) (G : Lp (EuclideanSpace ℝ (Fin d)) 2 μ)
    (hweak : ∀ᵐ ω ∂μ, HasWeakGradient Set.univ (orbit f ω)
      (fun x => (G (translate x ω)).ofLp)) :
    ∃ v : horizontalH1 μ hμ, (v : Lp ℝ 2 μ) = f ∧
      horizontalEuclideanGradient μ hμ v = G := by
  have hGm : Measurable (fun ω => (G ω).ofLp) :=
    (PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin d => ℝ)).measurable.comp
      (Lp.stronglyMeasurable G).measurable
  have hGc (i : Fin d) : MemLp (fun ω => G ω i) 2 μ :=
    (PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d => ℝ) i).comp_memLp' (Lp.memLp G)
  have hmem := horizontalH1_of_spatial_weakGradient μ hμ
    (Lp.stronglyMeasurable f).measurable hGm (Lp.memLp f) hGc hweak
  have hf : (Lp.memLp f).toLp f = f := Lp.toLp_coeFn f (Lp.memLp f)
  rw [hf] at hmem
  let v : horizontalH1 μ hμ := ⟨f, hmem⟩
  refine ⟨v, rfl, ?_⟩
  have hd := horizontalLpDerivatives_of_spatial_weakGradient μ hμ
    (Lp.stronglyMeasurable f).measurable hGm (Lp.memLp f) hGc hweak
  rw [hf] at hd
  have hcoord (i : Fin d) : horizontalH1Gradient μ hμ v i =
      (hGc i).toLp (fun ω => G ω i) :=
    (hasHorizontalLpDerivative_horizontalH1Gradient μ hμ v i).unique (hd i)
  apply Lp.ext
  have hae (i : Fin d) : (fun ω => horizontalEuclideanGradient μ hμ v ω i) =ᵐ[μ]
      fun ω => G ω i := by
    have hc := horizontalEuclideanGradient_coordinates μ hμ v i
    rw [hcoord i] at hc
    exact hc.trans (hGc i).coeFn_toLp
  filter_upwards [ae_all_iff.mpr hae] with ω hω
  ext i
  exact hω i

end EinsteinRelation.Correctors
