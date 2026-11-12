import EinsteinRelation.Correctors.ParabolicFluxSolution

open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Polarizing the proved energy identity gives the mixed flux pairing.
Source: `paper/main.tex:787–792,850`; AKM Proposition E.1 proof. -/
theorem IsParabolicFluxSolution.bilinear_energy_identity {d : ℕ}
    {I : Set ℝ} {U : Set (Vec d)} (hI : MeasurableSet I) (hU : IsOpen U)
    {u v : ℝ × Vec d → ℝ} {G H F J : ℝ × Vec d → Vec d}
    (hu : IsParabolicFluxSolution I U u G F)
    (hv : IsParabolicFluxSolution I U v H J)
    {ζ : ℝ × Vec d → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζc : HasCompactSupport ζ) (hζs : tsupport ζ ⊆ interior I ×ˢ U) :
    Integrable (fun z =>
      dot (F z) (fun j => ζ z ^ 2 * H z j + 2 * ζ z * v z * fderiv ℝ ζ z (0,unitVector j)) +
      dot (J z) (fun j => ζ z ^ 2 * G z j + 2 * ζ z * u z * fderiv ℝ ζ z (0,unitVector j)))
        (volume.restrict (I ×ˢ U)) ∧
    (∫ z in I ×ˢ U,
      dot (F z) (fun j => ζ z ^ 2 * H z j + 2 * ζ z * v z * fderiv ℝ ζ z (0,unitVector j)) +
      dot (J z) (fun j => ζ z ^ 2 * G z j + 2 * ζ z * u z * fderiv ℝ ζ z (0,unitVector j))) =
      2 * ∫ z in I ×ˢ U, u z * v z * ζ z * fderiv ℝ ζ z (1,0) := by
  let E := fun (w : ℝ × Vec d → ℝ) (D L : ℝ × Vec d → Vec d) z =>
    dot (L z) (fun j => ζ z ^ 2 * D z j + 2 * ζ z * w z * fderiv ℝ ζ z (0,unitVector j))
  let B := fun z =>
    dot (F z) (fun j => ζ z ^ 2 * H z j + 2 * ζ z * v z * fderiv ℝ ζ z (0,unitVector j)) +
    dot (J z) (fun j => ζ z ^ 2 * G z j + 2 * ζ z * u z * fderiv ℝ ζ z (0,unitVector j))
  have huE := hu.energy_identity hI hU hζ hζc hζs
  have hvE := hv.energy_identity hI hU hζ hζc hζs
  have hsE := (hu.sub hv).energy_identity hI hU hζ hζc hζs
  have hp (z : ℝ × Vec d) : B z = E u G F z + E v H J z -
      E (fun z => u z-v z) (fun z => G z-H z) (fun z => F z-J z) z := by
    dsimp [B, E, dot]
    simp_rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hBi : Integrable B (volume.restrict (I ×ˢ U)) := by
    apply ((huE.1.add hvE.1).sub hsE.1).congr
    exact Filter.Eventually.of_forall fun z => (hp z).symm
  refine ⟨hBi, ?_⟩
  have hζm : MemLp ζ ∞ (volume.restrict (I ×ˢ U)) :=
    hζ.continuous.memLp_top_of_hasCompactSupport hζc _
  have hDm : MemLp (fun z => fderiv ℝ ζ z (1,0)) ∞ (volume.restrict (I ×ˢ U)) :=
    ((contDiff_infty_iff_fderiv.mp hζ).2.clm_apply contDiff_const).continuous
      |>.memLp_top_of_hasCompactSupport (hζc.fderiv_apply ℝ (1,0)) _
  have hT {w w' : ℝ × Vec d → ℝ}
      (hw : MemLp w 2 (volume.restrict (I ×ˢ U)))
      (hw' : MemLp w' 2 (volume.restrict (I ×ˢ U))) :
      Integrable (fun z => w z * w' z * ζ z * fderiv ℝ ζ z (1,0))
        (volume.restrict (I ×ˢ U)) := by
    have hwζ : MemLp (fun z => w z * ζ z) 2 (volume.restrict (I ×ˢ U)) := hζm.mul' hw
    have hwD : MemLp (fun z => w' z * fderiv ℝ ζ z (1,0)) 2
        (volume.restrict (I ×ˢ U)) := hDm.mul' hw'
    convert hwζ.integrable_mul hwD using 1
    ext z
    dsimp
    ring
  have heq (z : ℝ × Vec d) :
      (u z)^2 * ζ z * fderiv ℝ ζ z (1,0) +
      (v z)^2 * ζ z * fderiv ℝ ζ z (1,0) -
      (u z-v z)^2 * ζ z * fderiv ℝ ζ z (1,0) =
      2 * (u z * v z * ζ z * fderiv ℝ ζ z (1,0)) := by ring
  change (∫ z in I ×ˢ U, B z) = _
  simp_rw [hp]
  dsimp only [E]
  simp only [Pi.sub_apply]
  have hlin := integral_sub (huE.1.add hvE.1) hsE.1
  simp only [Pi.add_apply, Pi.sub_apply] at hlin
  rw [hlin]
  have hadd := integral_add huE.1 hvE.1
  rw [hadd, huE.2, hvE.2]
  have hse := hsE.2
  simp only [Pi.sub_apply] at hse
  rw [hse]
  have htu : Integrable (fun z => (u z)^2 * ζ z * fderiv ℝ ζ z (1,0)) (volume.restrict (I ×ˢ U)) := by
    simpa only [pow_two] using hT hu.scalar_memLp hu.scalar_memLp
  have htv : Integrable (fun z => (v z)^2 * ζ z * fderiv ℝ ζ z (1,0)) (volume.restrict (I ×ˢ U)) := by
    simpa only [pow_two] using hT hv.scalar_memLp hv.scalar_memLp
  have hts : Integrable (fun z => (u z-v z)^2 * ζ z * fderiv ℝ ζ z (1,0)) (volume.restrict (I ×ˢ U)) := by
    simpa only [pow_two] using hT (hu.scalar_memLp.sub hv.scalar_memLp)
      (hu.scalar_memLp.sub hv.scalar_memLp)
  have hsum := integral_add htu htv
  have hsub := integral_sub (htu.add htv) hts
  simp only [Pi.add_apply] at hsub
  rw [← hsum, ← hsub]
  simp_rw [heq]
  exact integral_const_mul 2 _

end EinsteinRelation.Correctors
