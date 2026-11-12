import EinsteinRelation.Correctors.TensorLocalL2Support
import EinsteinRelation.Correctors.SpatialBallLocalL2Support
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM
/-- Source: `paper/main.tex:727-745`. Shrinking a ball decreases its
unnormalized root-integral of a nonnegative integrable function. -/
theorem sqrt_setIntegral_euclideanBall_mono {d : ℕ}
    (f : Vec d → ℝ) (z : Vec d) (r R : ℝ) (hrR : r ≤ R)
    (hf : IntegrableOn f (ball z R)) (hpos : ∀ x, 0 ≤ f x) :
    Real.sqrt (∫ x in ball z r, f x ∂volume) ≤
      Real.sqrt (∫ x in ball z R, f x ∂volume) := by
  apply Real.sqrt_le_sqrt
  exact setIntegral_mono_set hf (ae_of_all _ hpos)
    (Filter.Eventually.of_forall fun _ hx => lt_of_lt_of_le hx hrR)
/-- Source: `paper/main.tex:733-745`. Each local scalar entry norm is
controlled by the Frobenius root-integral on a larger concentric ball. -/
theorem sqrt_entry_integral_le_frobenius_on_larger_ball {d : ℕ}
    (S : Vec d → Mat d) (z : Vec d) (r R : ℝ) (hrR : r ≤ R)
    (hS : ∀ j k, MemLp (fun x => S x j k) 2 (volume.restrict (ball z R)))
    (j k : Fin d) :
    Real.sqrt (∫ x in ball z r, |S x j k| ^ 2 ∂volume) ≤
      Real.sqrt (∫ x in ball z R, frobeniusNorm (S x) ^ 2 ∂volume) := by
  apply le_trans ?_ (sqrt_integral_entry_sq_le_frobenius S hS j k)
  exact sqrt_setIntegral_euclideanBall_mono _ z r R hrR
    (by simpa only [sq_abs] using (hS j k).integrable_sq) (fun _ => sq_nonneg _)
end EinsteinRelation.Correctors
