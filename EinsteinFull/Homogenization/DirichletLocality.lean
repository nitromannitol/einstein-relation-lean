import EinsteinRelation.External.AKMEnergyDensitySources

/-!
# Locality of the Dirichlet energy

The variational quantity μ from Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, (1.7),
depends only on the almost-everywhere restriction of the coefficient field.
-/

open MeasureTheory

namespace EinsteinFull.Homogenization

open EinsteinRelation EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- Equal coefficients almost everywhere on a domain give the same Dirichlet energy. -/
theorem sourceDirichletEnergy_eq_of_ae_eq {d : ℕ} {K : ℝ}
    (a b : Coefficient d K) (U : Set (Vec d)) (e : Vec d)
    (h : (fun x => a x) =ᵐ[volume.restrict U] fun x => b x) :
    sourceDirichletEnergy a U e = sourceDirichletEnergy b U e := by
  have havg (g : Vec d → Vec d) :
      (⨍ x in U, (1 / 2 : ℝ) * dot (e + g x) ((a x).mulVec (e + g x)) ∂volume) =
        ⨍ x in U, (1 / 2 : ℝ) * dot (e + g x) ((b x).mulVec (e + g x)) ∂volume := by
    apply average_congr
    filter_upwards [h] with x hx
    rw [hx]
  unfold sourceDirichletEnergy
  congr 1
  ext E
  constructor
  · rintro ⟨u, g, hu, hE⟩
    exact ⟨u, g, hu, hE.trans (havg g)⟩
  · rintro ⟨u, g, hu, hE⟩
    exact ⟨u, g, hu, hE.trans (havg g).symm⟩

end EinsteinFull.Homogenization
