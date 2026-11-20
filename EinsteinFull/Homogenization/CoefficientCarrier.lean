import EinsteinRelation.Environment.AKMMeasurableRepresentative
import Homogenization.Probability.RegCoeffField.Sigma

/-!
# Coefficient carriers for homogenization

The locally integrable coefficient fields of Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, (0.6)–(0.11),
admit Borel representatives. The representatives preserve the smooth integral
observations defining the local coefficient sigma algebras.
-/

open MeasureTheory

namespace EinsteinFull.Homogenization

open EinsteinRelation EinsteinRelation.Environment.AKMTestIntegralSupport

attribute [local irreducible] coefficientRepresentative

/-- A Borel representative of a source coefficient as a regular coefficient field. -/
noncomputable def regularCoefficient {d : ℕ} {K : ℝ} (a : Coefficient d K) :
    _root_.Homogenization.RegCoeffField d where
  toFun := coefficientRepresentative a
  entry_measurable := by
    intro i j
    have h : Measurable (fun x : Vec d => (a, x)) :=
      (measurable_const : Measurable (fun _ : Vec d => a)).prodMk measurable_id
    have hm := measurable_coefficientRepresentative (d := d) (K := K)
    change @Measurable _ (Fin d → Fin d → ℝ) _ (borel _) _ at hm
    rw [← (Pi.borelSpace (X := fun _ : Fin d => Fin d → ℝ)).measurable_eq] at hm
    have he := (measurable_pi_iff.mp (measurable_pi_iff.mp hm i)) j
    exact he.comp h
  entry_locInt := by
    intro i j
    apply (a.locally_integrable i j).congr
    have h := (coefficientRepresentative_ae_eq a).symm
    filter_upwards [h] with x hx
    exact congrFun (congrFun hx i) j

/-- The regular coefficient is measurable for the full coefficient sigma algebras. -/
theorem measurable_regularCoefficient {d : ℕ} {K : ℝ} :
    Measurable (regularCoefficient (d := d) (K := K)) := by
  have hm := measurable_coefficientRepresentative (d := d) (K := K)
  change @Measurable _ (Fin d → Fin d → ℝ) _ (borel _) _ at hm
  rw [← (Pi.borelSpace (X := fun _ : Fin d => Fin d → ℝ)).measurable_eq] at hm
  have he (i j : Fin d) : Measurable (fun p : Coefficient d K × Vec d =>
      coefficientRepresentative p.1 p.2 i j) :=
    (measurable_pi_iff.mp (measurable_pi_iff.mp hm i)) j
  refine _root_.Homogenization.measurable_into_regCoeffField' ?_ ?_
  · intro x i j
    exact (he i j).comp (measurable_id.prodMk measurable_const)
  · intro i j φ hφ
    have h := (he i j).mul (hφ.measurable.comp measurable_snd)
    exact h.stronglyMeasurable.integral_prod_right'.measurable

/-- The representative and original coefficient agree almost everywhere. -/
theorem regularCoefficient_ae_eq {d : ℕ} {K : ℝ} (a : Coefficient d K) :
    (regularCoefficient a).toFun =ᵐ[volume] a.field :=
  coefficientRepresentative_ae_eq a

/-- Entry observations agree with the original source test integrals. -/
theorem entryTestR_regularCoefficient {d : ℕ} {K : ℝ} (a : Coefficient d K)
    (u : SmoothCompactTest d) (i j : Fin d) :
    _root_.Homogenization.entryTestR i j u (regularCoefficient a) = testIntegral a u i j := by
  unfold _root_.Homogenization.entryTestR testIntegral
  apply integral_congr_ae
  filter_upwards [regularCoefficient_ae_eq a] with x hx
  rw [congrFun (congrFun hx i) j, mul_comm]

/-- Every local smooth observation of the representative is locally measurable. -/
theorem measurable_entryTestR_regularCoefficient {d : ℕ} {K : ℝ}
    (U : Set (Vec d)) (u : SmoothCompactTest d) (hu : tsupport u.toFun ⊆ U)
    (i j : Fin d) :
    @Measurable (Coefficient d K) ℝ (localSigma U) inferInstance
      (fun a => _root_.Homogenization.entryTestR i j u (regularCoefficient a)) := by
  simp_rw [entryTestR_regularCoefficient]
  rw [measurable_iff_comap_le]
  exact le_iSup_of_le ⟨u, hu⟩ (le_iSup_of_le i (le_iSup_of_le j le_rfl))

end EinsteinFull.Homogenization
