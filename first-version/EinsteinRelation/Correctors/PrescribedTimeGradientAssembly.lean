import EinsteinRelation.Correctors.EuclideanLpCoordinateAssembly
import EinsteinRelation.Calculus.WeakRepresentativeOperations
import EinsteinRelation.TimeChange.EuclideanTransport

open MeasureTheory
namespace EinsteinRelation.Correctors

/-- Coordinate L² weak derivatives assemble into a Euclidean weak gradient.
Source: `paper/main.tex:798–806`; prescribed-time gradient recovery. -/
theorem exists_weakGradient_of_L2_partials {d : ℕ} (U : Set (Vec d))
    (u : Vec d → ℝ) (g : Fin d → Lp ℝ 2 (volume.restrict U))
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ i, ‖g i‖ ≤ B)
    (hw : ∀ i, HasWeakPartialDerivative U i u (g i)) :
    ∃ G : Vec d → Vec d, HasWeakGradient U u G ∧
      MemLp (fun x => euclideanNorm (G x)) 2 (volume.restrict U) ∧
      (eLpNorm (fun x => euclideanNorm (G x)) 2 (volume.restrict U)).toReal ≤
        Real.sqrt d * B := by
  obtain ⟨H,hH,henergy⟩ := exists_Lp_euclidean_of_coordinates (volume.restrict U) g
  let G : Vec d → Vec d := fun x => (H x).ofLp
  have hn (x : Vec d) : euclideanNorm (G x) = ‖H x‖ := by
    simpa [G] using TimeChange.euclideanNorm_eq_norm_toLp (G x)
  have hGL : MemLp (fun x => euclideanNorm (G x)) 2 (volume.restrict U) := by
    simpa only [hn] using (Lp.memLp H).norm
  refine ⟨G, ?_, hGL, ?_⟩
  · intro i
    exact (hw i).congr_ae (Filter.EventuallyEq.rfl) (hH i).symm
  · have hnLp : (eLpNorm (fun x => euclideanNorm (G x)) 2
        (volume.restrict U)).toReal = ‖H‖ := by
      simp only [hn, eLpNorm_norm, Lp.norm_def]
    rw [hnLp]
    have hs : ‖H‖^2 ≤ (d : ℝ) * B^2 := by
      rw [henergy]
      calc
        ∑ i : Fin d, ‖g i‖^2 ≤ ∑ _i : Fin d, B^2 :=
          Finset.sum_le_sum fun i _ => by nlinarith [hb i, norm_nonneg (g i)]
        _ = (d : ℝ) * B^2 := by simp
    have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
    have he : (Real.sqrt (d : ℝ) * B)^2 = (d : ℝ) * B^2 := by
      rw [mul_pow, Real.sq_sqrt hd]
    have hp : 0 ≤ Real.sqrt (d : ℝ) * B := mul_nonneg (Real.sqrt_nonneg _) hB
    nlinarith only [hs, he, hp, norm_nonneg H]

end EinsteinRelation.Correctors
