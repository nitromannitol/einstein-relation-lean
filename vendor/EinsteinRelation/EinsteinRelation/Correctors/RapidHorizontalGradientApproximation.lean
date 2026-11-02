import EinsteinRelation.Correctors.StationaryGradientDomainSupport
import Mathlib.Topology.Sequences
open MeasureTheory Filter Topology
open Set
namespace EinsteinRelation.Correctors

/-- Actual horizontal gradients approximate every closed-domain gradient rapidly;
source `paper/main.tex:693-698`. -/
theorem exists_rapid_horizontal_gradient_approximation {d : ℕ}
    (Q : Measure (FieldPair d)) (hQ : IsStationary Q)
    (G : Lp (EuclideanSpace ℝ (Fin d)) 2 Q)
    (hG : G ∈ stationaryPotentialGradientSubmodule Q hQ) :
    ∃ f : ℕ → horizontalH1 Q hQ, ∀ n,
      ‖horizontalEuclideanGradient Q hQ (f n) - G‖ ≤ (1 / 2 : ℝ) ^ n := by
  have hG_mem : G ∈ (LinearMap.range (horizontalEuclideanGradientMap Q hQ)).topologicalClosure := hG
  have hpos : ∀ n : ℕ, (0 : ℝ) < (1 / 2 : ℝ) ^ n := fun n => pow_pos (by norm_num) n
  have h_exists : ∀ n : ℕ, ∃ f : horizontalH1 Q hQ,
      ‖horizontalEuclideanGradient Q hQ f - G‖ < (1 / 2 : ℝ) ^ n := by
    intro n
    have hpos_n := hpos n
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe, Metric.mem_closure_iff] at hG_mem
    obtain ⟨U, hU_mem, hdistU⟩ := hG_mem ((1 / 2 : ℝ) ^ n) hpos_n
    obtain ⟨f, hf⟩ := hU_mem
    refine ⟨f, ?_⟩
    rw [← hf, dist_eq_norm, norm_sub_rev] at hdistU
    exact hdistU
  choose f hf using h_exists
  refine ⟨f, fun n => (hf n).le⟩
