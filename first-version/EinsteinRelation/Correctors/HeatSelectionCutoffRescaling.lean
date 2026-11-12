import EinsteinRelation.Correctors.IndependentCutoffErrors
import EinsteinRelation.Correctors.CutoffCofinalMesh
import EinsteinRelation.Correctors.PositiveWindowDecomposition

/-! Source: `paper/main.tex:722,756`. Independent heat cutoffs survive
physical time rescaling when both actual endpoint errors vanish locally. -/
open MeasureTheory Filter Topology
open scoped ENNReal
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM HeatSelectedSkewMeaning

/-- The literal space-first heat integral on a rescaled finite time window. -/
def rescaledAKMHeatGradientTruncation {d : ℕ} (g : Vec d → Vec d)
    (c : ℝ) (m n : ℕ) (j k l : Fin d) (x : Vec d) : ℝ :=
  ∫ t in Set.Icc (c / ((m : ℝ) + 1)) (c * ((n : ℝ) + 1)),
    akmHeatGradientSpaceIntegral g t j k l x

/-- Cofinal source windows and vanishing endpoint errors preserve the
independent local L² limit of the actual heat integrals. -/
theorem heat_selection_rescaled_local_L2_of_endpoint_errors {d : ℕ}
    (g : Vec d → Vec d) (G : Fin d → Fin d → Vec d → Vec d)
    (hselect : IsHeatSelectedFluxGradient g G) (c : ℝ) (hc : 0 < c)
    (j k l : Fin d) (R : ℕ)
    (hlower :
      (∀ m : ℕ, MemLp (fun x => ∫ t in
        Set.Icc (((⌊(c / ((m : ℝ) + 1))⁻¹⌋₊ + 1 : ℕ) : ℝ))⁻¹
          (c / ((m : ℝ) + 1)), akmHeatGradientSpaceIntegral g t j k l x)
            2 (volume.restrict (ball 0 ((R : ℝ) + 1)))) ∧
      Tendsto (fun m : ℕ => eLpNorm (fun x => ∫ t in
        Set.Icc (((⌊(c / ((m : ℝ) + 1))⁻¹⌋₊ + 1 : ℕ) : ℝ))⁻¹
          (c / ((m : ℝ) + 1)), akmHeatGradientSpaceIntegral g t j k l x)
            2 (volume.restrict (ball 0 ((R : ℝ) + 1)))) atTop (𝓝 0))
    (hupper :
      (∀ n : ℕ, MemLp (fun x => ∫ t in
        Set.Icc (c * ((n : ℝ) + 1)) ((⌊c * ((n : ℝ) + 1)⌋₊ + 1 : ℕ) : ℝ),
          akmHeatGradientSpaceIntegral g t j k l x)
            2 (volume.restrict (ball 0 ((R : ℝ) + 1)))) ∧
      Tendsto (fun n : ℕ => eLpNorm (fun x => ∫ t in
        Set.Icc (c * ((n : ℝ) + 1)) ((⌊c * ((n : ℝ) + 1)⌋₊ + 1 : ℕ) : ℝ),
          akmHeatGradientSpaceIntegral g t j k l x)
            2 (volume.restrict (ball 0 ((R : ℝ) + 1)))) atTop (𝓝 0)) :
    (∀ m n, MemLp (rescaledAKMHeatGradientTruncation g c m n j k l)
      2 (volume.restrict (ball 0 ((R : ℝ) + 1)))) ∧
    Tendsto (fun mn : ℕ × ℕ => eLpNorm
      (fun x => rescaledAKMHeatGradientTruncation g c mn.1 mn.2 j k l x - G j k x l)
        2 (volume.restrict (ball 0 ((R : ℝ) + 1)))) atTop (𝓝 0) := by
  let μ : Measure (Vec d) := volume.restrict (ball 0 ((R : ℝ) + 1))
  let a (m : ℕ) : ℕ := ⌊((m : ℝ) + 1) / c⌋₊
  let b (n : ℕ) : ℕ := ⌊c * ((n : ℝ) + 1)⌋₊
  let E (m : ℕ) (x : Vec d) : ℝ := -(∫ t in
    Set.Icc (((⌊(c / ((m : ℝ) + 1))⁻¹⌋₊ + 1 : ℕ) : ℝ))⁻¹
      (c / ((m : ℝ) + 1)), akmHeatGradientSpaceIntegral g t j k l x)
  let F (n : ℕ) (x : Vec d) : ℝ := -(∫ t in
    Set.Icc (c * ((n : ℝ) + 1)) ((⌊c * ((n : ℝ) + 1)⌋₊ + 1 : ℕ) : ℝ),
      akmHeatGradientSpaceIntegral g t j k l x)
  have hsrc := hselect j k l R
  have hcofinal := tendsto_rescaled_cutoff_mesh_atTop c hc
  apply local_L2_limit_of_independent_endpoint_errors μ
    (fun m n => iteratedAKMHeatGradientTruncation g m n j k l)
    (fun m n => rescaledAKMHeatGradientTruncation g c m n j k l)
    (fun x => G j k x l) E F a b hcofinal.2 hcofinal.1
    hsrc.2.1 hsrc.2.2.1 (fun m => (hlower.1 m).neg) (fun n => (hupper.1 n).neg)
    ?_ hsrc.2.2.2 ?_ ?_
  · intro m n
    filter_upwards [hsrc.1 (a m) (b n)] with x hx
    have hsmall := (cutoff_nearest_mesh_ratios
      (div_pos hc (by positivity : 0 < (m : ℝ) + 1))).2
    have hlarge := (cutoff_nearest_mesh_ratios
      (mul_pos hc (by positivity : 0 < (n : ℝ) + 1))).1
    have hmiddle : c / ((m : ℝ) + 1) ≤ c * ((n : ℝ) + 1) := by
      have hleft : c / ((m : ℝ) + 1) ≤ c :=
        div_le_self hc.le (by linarith [show (0 : ℝ) ≤ (m : ℝ) from Nat.cast_nonneg m])
      have hright : c ≤ c * ((n : ℝ) + 1) := by
        nlinarith [show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n]
      exact hleft.trans hright
    have ha : (((⌊(c / ((m : ℝ) + 1))⁻¹⌋₊ + 1 : ℕ) : ℝ))⁻¹ =
        (((a m + 1 : ℕ) : ℝ))⁻¹ := by simp only [a, inv_div]
    have hid := integral_Icc_remove_endpoint_windows
      (fun t => akmHeatGradientSpaceIntegral g t j k l x)
      _ _ _ _ hsmall.2.1.le hmiddle hlarge.2.1.le
      (by simpa only [ha, b] using hx.2)
    simpa only [rescaledAKMHeatGradientTruncation, iteratedAKMHeatGradientTruncation,
      E, F, ha, b, sub_eq_add_neg] using hid
  · have hE (m : ℕ) : eLpNorm (E m) 2 μ = eLpNorm (fun x => ∫ t in
        Set.Icc (((⌊(c / ((m : ℝ) + 1))⁻¹⌋₊ + 1 : ℕ) : ℝ))⁻¹
          (c / ((m : ℝ) + 1)), akmHeatGradientSpaceIntegral g t j k l x) 2 μ :=
        eLpNorm_neg _ _ _
    simpa only [hE] using hlower.2
  · have hF (n : ℕ) : eLpNorm (F n) 2 μ = eLpNorm (fun x => ∫ t in
        Set.Icc (c * ((n : ℝ) + 1)) ((⌊c * ((n : ℝ) + 1)⌋₊ + 1 : ℕ) : ℝ),
          akmHeatGradientSpaceIntegral g t j k l x) 2 μ := eLpNorm_neg _ _ _
    simpa only [hF] using hupper.2

end EinsteinRelation.Correctors
