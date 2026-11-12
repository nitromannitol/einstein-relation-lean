import EinsteinRelation.Correctors.PlanarContinuousBallSupport
import EinsteinRelation.Correctors.SpatialWeakLocalization
/-! Comparison with an explicit affine reference for marginal integrability.
Source: `paper/main.tex:872–894`. -/
open MeasureTheory
open scoped Matrix
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger
/-- A skew potential whose row divergence is minus the mean flux.
Source: `paper/main.tex:872–883`. -/
noncomputable def planarAffineSkewReference (m : Vec 2) (x : Vec 2) : Mat 2 :=
  !![0, m 1*x 0-m 0*x 1; -(m 1*x 0-m 0*x 1), 0]

/-- Subtracting the affine reference turns the total gradient into the
paired homogeneous quantity. Source: `paper/main.tex:872–883`. -/
theorem planar_single_centered_amplitude_of_reference
    (h817 : LocalBoundednessEstimate) (hP : BallPoincareEstimate)
    {L : ℝ} (hL : 0 < L) :
    ∃ C : ℝ, 0 < C ∧ ∀ (i : Fin 2) (m : Vec 2),
      HasWeakGradient Set.univ (fun x : Vec 2 => -(x i)) (fun _ => -(unitVector i)) →
      HasWeakRowDivergence Set.univ (planarAffineSkewReference m) (fun _ => -m) →
      ∀ (R : ℝ), 0 < R → ∀ (a : Vec 2 → Mat 2)
        (u : Vec 2 → ℝ) (G : Vec 2 → Vec 2) (S : Vec 2 → Mat 2),
      IsElliptic L a → Continuous a → Continuous u → Continuous S →
      (∀ x, (S x).transpose = -(S x)) →
      MemLp (fun x => euclideanNorm (unitVector i+G x)) 2
        (volume.restrict (ball 0 (2*R))) →
      HasWeakGradient Set.univ u G →
      HasWeakDivergence Set.univ (fun x => (a x).mulVec (unitVector i+G x)) (fun _ => 0) →
      HasWeakRowDivergence Set.univ S (fun x => (a x).mulVec (unitVector i+G x)-m) →
      ∀ w : Vec 2 → ℝ, Continuous w → HasCompactSupport w →
      (∀ x, 0 ≤ w x) → (∫ x, w x) = 1 → Function.support w ⊆ ball 0 R →
      |(u 0-∫ x, w x*u x)-(-∫ x, w x*(-(x i)))| +
        frobeniusNorm (Matrix.of (fun j k => (S 0 j k-∫ x, w x*S x j k)-
          (-∫ x, w x*planarAffineSkewReference m x j k))) ≤
        C*R * vectorRms volume (ball 0 (2*R)) (fun x => unitVector i+G x) := by
  obtain ⟨C,hC,hb⟩ := paired_planar_centered_correctors_of_gt h817 hP hL
  refine ⟨C,hC,?_⟩
  intro i m href hrref R hR a u G S ha hac hu hS hsk hG hg hd hr w hw hws hw0 hw1 hwsb
  have hrefc : Continuous (fun x : Vec 2 => -(x i)) := by fun_prop
  have hSc : Continuous (planarAffineSkewReference m) := by
    apply continuous_pi; intro j
    apply continuous_pi; intro k
    fin_cases j <;> fin_cases k
    · exact continuous_const
    · change Continuous (fun x : Vec 2 => m 1*x 0-m 0*x 1)
      fun_prop
    · change Continuous (fun x : Vec 2 => -(m 1*x 0-m 0*x 1))
      fun_prop
    · exact continuous_const
  have hSentry (j k : Fin 2) : Continuous (fun x => S x j k) := by
    exact (continuous_apply k).comp ((continuous_apply j).comp hS)
  have hSrefentry (j k : Fin 2) : Continuous (fun x => planarAffineSkewReference m x j k) := by
    exact (continuous_apply k).comp ((continuous_apply j).comp hSc)
  have hiu : Integrable (fun x => w x*u x) volume := (hw.mul hu).integrable_of_hasCompactSupport hws.mul_right
  have hiref : Integrable (fun x => w x*(-(x i))) volume := (hw.mul hrefc).integrable_of_hasCompactSupport hws.mul_right
  have hiS (j k : Fin 2) : Integrable (fun x => w x*S x j k) volume := (hw.mul (hSentry j k)).integrable_of_hasCompactSupport hws.mul_right
  have hiSref (j k : Fin 2) : Integrable (fun x => w x*planarAffineSkewReference m x j k) volume := (hw.mul (hSrefentry j k)).integrable_of_hasCompactSupport hws.mul_right
  have hb' := hb R hR a a (unitVector i) m u (fun x => -(x i)) G
    (fun _ => -(unitVector i)) S (planarAffineSkewReference m) ha hac (fun _ _ => rfl)
    (continuous_memLp_euclideanBall _ hu _) (continuous_memLp_euclideanBall _ hrefc _)
    (by simpa only [sub_neg_eq_add, add_comm] using hG)
    (hasWeakGradient_mono (Set.subset_univ _) hg)
    (hasWeakGradient_mono (Set.subset_univ _) href)
    (hasWeakDivergence_mono (Set.subset_univ _) hd)
    (by simpa only [add_neg_cancel, Matrix.mulVec_zero] using hasWeakDivergence_zero (ball (0 : Vec 2) (2*R)))
    hsk (by intro x; ext j k; fin_cases j <;> fin_cases k <;> simp [planarAffineSkewReference])
    (fun j => hasWeakDivergence_mono (Set.subset_univ _) (hr j))
    (by simpa only [add_neg_cancel, Matrix.mulVec_zero, zero_sub] using
      (fun j => hasWeakDivergence_mono (Set.subset_univ _) (hrref j)))
    (continuous_memLp_euclideanBall _ ((hSentry 0 1).sub (hSrefentry 0 1)) _)
    (hu.sub hrefc).continuousOn ((hSentry 0 1).sub (hSrefentry 0 1)).continuousOn
    w (hw.integrable_of_hasCompactSupport hws)
    (by simpa only [mul_sub] using hiu.sub hiref)
    (fun j k => by simpa only [mul_sub] using (hiS j k).sub (hiSref j k))
    hw0 hw1 hwsb 0 (by simpa [ball, euclideanNorm, euclideanSq, dot] using hR)
  have hscalar := centered_pair_subtraction volume u (fun x => -(x i)) w 0 hiu hiref
  have hmatrix : Matrix.of (fun j k => (S 0 j k-∫ x, w x*S x j k)-
      (-∫ x, w x*planarAffineSkewReference m x j k)) =
      Matrix.of (fun j k => (S 0 j k-planarAffineSkewReference m 0 j k)-
        ∫ x, w x*(S x j k-planarAffineSkewReference m x j k)) := by
    ext j k
    have hz (a b : Fin 2) : planarAffineSkewReference m 0 a b = 0 := by
      fin_cases a <;> fin_cases b <;> simp [planarAffineSkewReference]
    simpa only [hz, zero_sub] using centered_pair_subtraction volume
      (fun x => S x j k) (fun x => planarAffineSkewReference m x j k) w 0
      (hiS j k) (hiSref j k)
  rw [hmatrix]
  have hscalar' : (u 0-∫ x, w x*u x)-(-∫ x, w x*(-(x i))) =
      (u 0-(-(0 : Vec 2) i))-∫ x, w x*(u x-(-(x i))) := by simpa using hscalar
  rw [hscalar']
  simpa only [sub_neg_eq_add, add_comm] using hb'
end EinsteinRelation.Correctors
