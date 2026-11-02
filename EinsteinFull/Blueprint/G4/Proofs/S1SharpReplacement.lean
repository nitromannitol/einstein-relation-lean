import EinsteinFull.Blueprint.G4.node_sharp_u2E_example_u23_replacement_u2D_pair
import EinsteinFull.Blueprint.G4.node_app_u3A_sharp_u2D_fields
import EinsteinFull.Calculus.S1SharpReplaceBounds

/-! Reduction of graph node `sharp.example#replacement-pair`, `paper/main.tex:1565`, to its
dependency `app:sharp-fields`. The replacement `F` is the pointwise map
`ω ↦ (a/a₁₁, -(1/2) log a₁₁)` (clamped below, which is immaterial on the closed event
`a₁₁ ≥ 1/3` that carries the law); it is Borel, local and translation equivariant, and the
smoothness and regularity data of the image law come from uniform derivative bounds. -/

open MeasureTheory

namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.Sharpness
open EinsteinFull.Calculus.S1

private theorem continuous_a11 {d : ℕ} (first : Fin d) (x : Vec d) :
    Continuous fun ω : FieldPair d => reducedCoefficient ω x first first :=
  (Real.continuous_exp.comp (continuous_const.mul
    ((continuous_eval_const x).comp continuous_snd))).mul
    (((continuous_eval_const x).comp continuous_fst).matrix_elem first first)

private theorem isClosed_a11_ge {d : ℕ} (first : Fin d) :
    IsClosed {ω : FieldPair d | ∀ x, (1 / 3 : ℝ) ≤ reducedCoefficient ω x first first} := by
  have : {ω : FieldPair d | ∀ x, (1 / 3 : ℝ) ≤ reducedCoefficient ω x first first} =
      ⋂ x : Vec d, {ω : FieldPair d | (1 / 3 : ℝ) ≤ reducedCoefficient ω x first first} := by
    ext ω
    simp
  rw [this]
  exact isClosed_iInter fun x => isClosed_le continuous_const (continuous_a11 first x)

private theorem replacePair_reducedCoefficient_eq {d : ℕ} (first : Fin d) (ω : FieldPair d)
    (hω : ∀ x, (1 / 3 : ℝ) ≤ reducedCoefficient ω x first first) (x : Vec d) :
    reducedCoefficient (replacePair first ω) x = reducedCoefficient ω x := by
  have hpos : 0 < reducedCoefficient ω x first first := by linarith [hω x]
  have hmax : max (reducedCoefficient ω x first first) (1 / 4) =
      reducedCoefficient ω x first first := max_eq_left (by linarith [hω x])
  have h1 : (replacePair first ω).1 x =
      (reducedCoefficient ω x first first)⁻¹ • reducedCoefficient ω x := by
    rw [replacePair_fst, hmax]
  have h2 : clockDensity (replacePair first ω) x = reducedCoefficient ω x first first := by
    unfold clockDensity
    rw [replacePair_snd, hmax,
      show (-2 : ℝ) * (-(1 / 2 : ℝ) * Real.log (reducedCoefficient ω x first first)) =
        Real.log (reducedCoefficient ω x first first) by ring, Real.exp_log hpos]
  show clockDensity (replacePair first ω) x • (replacePair first ω).1 x = _
  rw [h2, h1, smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]

theorem node_sharp_u2E_example_u23_replacement_u2D_pair_of_deps
    (_hfields : node_app_u3A_sharp_u2D_fieldsStmt) :
    node_sharp_u2E_example_u23_replacement_u2D_pairStmt := by
  intro d hd P hP first D Q hQ
  have hF := measurable_replacePair first
  have hFphys := EinsteinFull.Work.W8.measurable_physicalPair first
  obtain ⟨Λ, hΛ9, hreg⟩ := exists_replacePair_regular first
  obtain ⟨Dn, S, hr, -, hregD, hSm, hSmem, hSb⟩ := exists_data_of_family
    (fun W : NoiseSample d => replacePair first (EinsteinFull.Work.W8.physicalPair first W))
    (replacePair_unifBdd first).1 (replacePair_unifBdd first).2
    (replacePair_isSmoothFieldPair first) (by linarith) D.one_le_dependenceRange hreg
  have hae : ∀ p : Set (FieldPair d), MeasurableSet p →
      (∀ W : NoiseSample d, replacePair first (EinsteinFull.Work.W8.physicalPair first W) ∈ p) →
      ∀ᵐ ω' ∂(Q.measure.map (replacePair first)), ω' ∈ p := fun p hp h =>
    (ae_map_iff hF.aemeasurable hp).mpr (by
      rw [hQ]
      exact (ae_map_iff hFphys.aemeasurable (hF hp)).mpr (ae_of_all P h))
  have hA : ∀ᵐ ω ∂Q.measure, ∀ x, (1 / 3 : ℝ) ≤ reducedCoefficient ω x first first := by
    rw [hQ]
    exact (ae_map_iff hFphys.aemeasurable (isClosed_a11_ge first).measurableSet).mpr
      (ae_of_all P fun W x => (a11_mem_Icc first W x).1)
  refine ⟨Dn, replacePair first, hF, ?_, ?_⟩
  · filter_upwards [hA] with ω hω x
    have hpos : 0 < reducedCoefficient ω x first first := by linarith [hω x]
    have hmax : max (reducedCoefficient ω x first first) (1 / 4) =
        reducedCoefficient ω x first first := max_eq_left (by linarith [hω x])
    have hred := replacePair_reducedCoefficient_eq first ω hω
    refine ⟨by rw [replacePair_fst, hmax], by rw [replacePair_snd, hmax], hpos, ?_, hred x, ?_⟩
    · unfold clockDensity
      rw [replacePair_snd, hmax,
        show (-2 : ℝ) * (-(1 / 2 : ℝ) * Real.log (reducedCoefficient ω x first first)) =
          Real.log (reducedCoefficient ω x first first) by ring, Real.exp_log hpos]
    · intro lam f
      have hfun : reducedCoefficient (replacePair first ω) = reducedCoefficient ω := funext hred
      unfold reducedGenerator
      rw [hfun]
  · haveI : IsProbabilityMeasure Q.measure := Q.probability
    let Qn : EnvironmentLaw d Dn.ellipticity Dn.dependenceRange :=
      { measure := Q.measure.map (replacePair first)
        probability := inferInstance
        ellipticity_parameter := Dn.one_le_ellipticity
        range_parameter := Dn.one_le_dependenceRange
        regular := hae {ω | IsRegular Dn.ellipticity ω}
          (measurableSet_isRegular_fieldPair Dn.ellipticity) hregD
        stationary := isStationary_map_replacePair first Q.stationary
        finiteRange := by
          rw [hr]
          exact hasFiniteRange_map_replacePair first Q.finiteRange }
    exact ⟨Qn, rfl, (hae S hSm hSmem).mono fun ω hω => hSb ω hω⟩

end EinsteinFull.Blueprint
