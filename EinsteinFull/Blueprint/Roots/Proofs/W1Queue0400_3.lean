import EinsteinFull.Blueprint.Roots.node_l_u3A_forced_u2D_local
import EinsteinFull.Blueprint.Foundation.node_e_u3A_local_u2D_time
import EinsteinFull.Blueprint.G2.node_e_u3A_holder_u2D_average
import EinsteinFull.Blueprint.Foundation.node_e_u3A_forced_u2D_locality
import EinsteinFull.Blueprint.Foundation.node_l_u3A_forced_u2D_local_u23_point_u2D_kernel
import EinsteinFull.Calculus.ComplexGeneratorUniquenessSupport

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Combine local energy, Gaussian unsmoothing and local approximants for the
same actual endpoint. The graph's point-kernel dependency is already included
in the stronger deterministic conclusion of the locality contract. -/
@[nolint unusedArguments]
theorem node_l_u3A_forced_u2D_local_of_deps
    (htime : node_e_u3A_local_u2D_timeStmt)
    (hholder : node_e_u3A_holder_u2D_averageStmt)
    (hlocal : node_e_u3A_forced_u2D_localityStmt)
    (_hkernel : node_l_u3A_forced_u2D_local_u23_point_u2D_kernelStmt) :
    node_l_u3A_forced_u2D_localStmt := by
  intro d hd D
  obtain ⟨α, hα, hholder⟩ := hholder d hd D
  obtain ⟨Cdet, c, N, hCdet, hc, hlocal⟩ := hlocal d hd D
  refine ⟨α, Cdet, c, N, hα, hCdet, hc, ?_⟩
  intro p hp
  obtain ⟨C₁, Cp₁, hC₁, hCp₁, htime⟩ := htime d hd D p hp
  obtain ⟨C₂, Cp₂, hC₂, hCp₂, hholder⟩ := hholder p hp
  let C := max C₁ C₂
  let Cp := max Cp₁ Cp₂
  have hC : 1 ≤ C := hC₁.trans (le_max_left _ _)
  have hCp : 0 < Cp := hCp₁.trans_le (le_max_left _ _)
  refine ⟨C, Cp, hC, hCp, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  obtain ⟨G, V, hGV, henergy⟩ := htime Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  obtain ⟨Gl, hGl, happrox, hbound⟩ := hlocal Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  have hG (t : ℝ≥0) (ht : 0 < (t : ℝ)) : G t = Gl t :=
    (hGV t ht).1.unique (hGl t ht).1
  refine ⟨G, V, hGV, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨hmem, he⟩ := henergy t ht
    obtain ⟨_, hh⟩ := hholder Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν t ht
    refine ⟨hmem, ?_, ?_⟩
    · intro ρ x hρ
      obtain ⟨hm, hb⟩ := he ρ x hρ
      refine ⟨hm, hb.trans ?_⟩
      have hbase : 1 ≤ 1 + ‖ζ‖ * Real.sqrt (t : ℝ) :=
        le_add_of_nonneg_right (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
      gcongr
      · exact le_max_left C₁ C₂
      · exact le_max_left C₁ C₂
      · exact le_max_left Cp₁ Cp₂
    · intro b hb hb₁ hbt
      obtain ⟨hm, hest⟩ := hh b hb hb₁ hbt
      refine ⟨hm, hest.trans ?_⟩
      have hbase : 1 ≤ 1 + ‖ζ‖ * Real.sqrt (t : ℝ) :=
        le_add_of_nonneg_right (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
      gcongr
      · exact le_max_right C₁ C₂
      · exact le_max_right C₁ C₂
      · exact le_max_right Cp₁ Cp₂
  · intro t ht ρ hρ
    rw [hG t (lt_of_lt_of_le zero_lt_one ht)]
    exact happrox t ht ρ hρ
  · intro t ht hζ
    rw [hG t ht]
    exact hbound t ht hζ

end EinsteinFull.Blueprint
