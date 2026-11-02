import EinsteinFull.Calculus.C8GMPMartingale
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
open MeasureTheory Filter Set ProbabilityTheory
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation
open EinsteinRelation.SpatialDirichlet
open EinsteinRelation.External.GantertSection7Support
open EinsteinFull.C8GMP
open scoped InnerProductSpace Matrix


/- The local polarization proof reuses PhysicalFormPolarizationSupport. Its
PhysicalResolventExistenceSupport import does not elaborate under Lean 4.35;
none of that import is needed for the argument below. -/
private theorem sourceDot_comm {d : ℕ} (u v : Vec d) : dot u v = dot v u := by
  unfold dot
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

private theorem sourceDot_add_left {d : ℕ} (u v w : Vec d) :
    dot (u + v) w = dot u w + dot v w := by
  simp only [dot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem sourceDot_add_right {d : ℕ} (u v w : Vec d) :
    dot u (v + w) = dot u v + dot u w := by
  simp only [dot, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private theorem sourceDot_sub_left {d : ℕ} (u v w : Vec d) :
    dot (u - v) w = dot u w - dot v w := by
  simp only [dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

private theorem sourceDot_sub_right {d : ℕ} (u v w : Vec d) :
    dot u (v - w) = dot u v - dot u w := by
  simp only [dot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

private theorem sourceDot_matrix_symmetric {d : ℕ} (A : Mat d)
    (hA : A.transpose = A) (u v : Vec d) :
    dot u (A.mulVec v) = dot v (A.mulVec u) := by
  have hu : Matrix.vecMul u A = A.mulVec u := by
    calc
      Matrix.vecMul u A = Matrix.vecMul u A.transpose.transpose := by
        rw [Matrix.transpose_transpose]
      _ = A.transpose.mulVec u := Matrix.vecMul_transpose A.transpose u
      _ = A.mulVec u := by rw [hA]
  calc
    dot u (A.mulVec v) = dotProduct (Matrix.vecMul u A) v := by
      change dotProduct u (A.mulVec v) = _
      exact Matrix.dotProduct_mulVec u A v
    _ = dot (A.mulVec u) v := by
      rw [hu]
      rfl
    _ = dot v (A.mulVec u) := sourceDot_comm _ _

private theorem sourceDot_mulVec_quadratic_polarization {d : ℕ} (A : Mat d)
    (hA : A.transpose = A) (u v : Vec d) :
    dot (u + v) (A.mulVec (u + v)) - dot (u - v) (A.mulVec (u - v)) =
      4 * dot u (A.mulVec v) := by
  simp only [Matrix.mulVec_add, Matrix.mulVec_sub, sourceDot_add_left,
    sourceDot_add_right, sourceDot_sub_left, sourceDot_sub_right]
  rw [sourceDot_matrix_symmetric A hA u v]
  ring

private theorem representativeGradient_eq_spaceGradient {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    (u : densityWeightedH1Submodule ρ hρ hρpos) :
    (densityWeightedH1SpaceRepresentative ρ hρ hρpos u).gradient_memLp.toLp
      (densityWeightedH1SpaceRepresentative ρ hρ hρpos u).weakGradient =
      densityWeightedH1SpaceGradient u := by
  have h := congrArg Prod.snd (densityWeightedH1SpaceRepresentative_pair u)
  change _ = _ at h
  exact h

private theorem sourcePhysicalGraph_gradient_add_ae {d : ℕ}
    (ρ : Vec d → ℝ) (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    (σ : Vec d → ℝ) (K : ℝ)
    (hMeasure : densityWeightedMeasure σ ≤
      ENNReal.ofReal K • densityWeightedMeasure ρ)
    (u v : densityWeightedH1Submodule ρ hρ hρpos) :
    (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure (u + v)).weakGradient =ᵐ[
      densityWeightedMeasure σ] fun x =>
        (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u).weakGradient x +
          (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure v).weakGradient x := by
  let gu := densityWeightedH1SpaceRepresentative ρ hρ hρpos u
  let gv := densityWeightedH1SpaceRepresentative ρ hρ hρpos v
  let gs := densityWeightedH1SpaceRepresentative ρ hρ hρpos (u + v)
  let E := WithLp.prodContinuousLinearEquiv 2 ℝ
    (Lp ℝ 2 (densityWeightedMeasure ρ))
    (Lp (EuclideanSpace ℝ (Fin d)) 2 (densityWeightedMeasure ρ))
  have hLp : gs.gradient_memLp.toLp gs.weakGradient =
      gu.gradient_memLp.toLp gu.weakGradient + gv.gradient_memLp.toLp gv.weakGradient := by
    rw [representativeGradient_eq_spaceGradient ρ hρ hρpos (u + v),
      representativeGradient_eq_spaceGradient ρ hρ hρpos u,
      representativeGradient_eq_spaceGradient ρ hρ hρpos v]
    change (E (u + v).1).2 = (E u.1).2 + (E v.1).2
    exact congrArg Prod.snd (E.map_add u.1 v.1)
  have hae := Lp.ext_iff.mp hLp
  have hAE : gs.weakGradient =ᵐ[densityWeightedMeasure ρ] fun x =>
      gu.weakGradient x + gv.weakGradient x := by
    filter_upwards [hae, Lp.coeFn_add
      (gu.gradient_memLp.toLp gu.weakGradient)
      (gv.gradient_memLp.toLp gv.weakGradient), gs.gradient_memLp.coeFn_toLp,
      gu.gradient_memLp.coeFn_toLp, gv.gradient_memLp.coeFn_toLp] with x heq hadd hs hu hv
    calc
      gs.weakGradient x = (gs.gradient_memLp.toLp gs.weakGradient) x := hs.symm
      _ = ((gu.gradient_memLp.toLp gu.weakGradient) +
        (gv.gradient_memLp.toLp gv.weakGradient)) x := heq
      _ = (gu.gradient_memLp.toLp gu.weakGradient) x +
        (gv.gradient_memLp.toLp gv.weakGradient) x := hadd
      _ = gu.weakGradient x + gv.weakGradient x := by rw [hu, hv]
  have hσ := (Measure.absolutelyContinuous_of_le_smul hMeasure).ae_eq hAE
  calc
    (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure (u + v)).weakGradient =ᵐ[
        densityWeightedMeasure σ] gs.weakGradient := Filter.Eventually.of_forall fun _ => rfl
    _ =ᵐ[densityWeightedMeasure σ] fun x => gu.weakGradient x + gv.weakGradient x := hσ
    _ =ᵐ[densityWeightedMeasure σ] fun x =>
        (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u).weakGradient x +
          (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure v).weakGradient x :=
      Filter.Eventually.of_forall fun _ => rfl

private theorem sourcePhysicalGraph_gradient_sub_ae {d : ℕ}
    (ρ : Vec d → ℝ) (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    (σ : Vec d → ℝ) (K : ℝ)
    (hMeasure : densityWeightedMeasure σ ≤
      ENNReal.ofReal K • densityWeightedMeasure ρ)
    (u v : densityWeightedH1Submodule ρ hρ hρpos) :
    (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure (u - v)).weakGradient =ᵐ[
      densityWeightedMeasure σ] fun x =>
        (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u).weakGradient x -
          (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure v).weakGradient x := by
  let gu := densityWeightedH1SpaceRepresentative ρ hρ hρpos u
  let gv := densityWeightedH1SpaceRepresentative ρ hρ hρpos v
  let gd := densityWeightedH1SpaceRepresentative ρ hρ hρpos (u - v)
  let E := WithLp.prodContinuousLinearEquiv 2 ℝ
    (Lp ℝ 2 (densityWeightedMeasure ρ))
    (Lp (EuclideanSpace ℝ (Fin d)) 2 (densityWeightedMeasure ρ))
  have hLp : gd.gradient_memLp.toLp gd.weakGradient =
      gu.gradient_memLp.toLp gu.weakGradient - gv.gradient_memLp.toLp gv.weakGradient := by
    rw [representativeGradient_eq_spaceGradient ρ hρ hρpos (u - v),
      representativeGradient_eq_spaceGradient ρ hρ hρpos u,
      representativeGradient_eq_spaceGradient ρ hρ hρpos v]
    change (E (u - v).1).2 = (E u.1).2 - (E v.1).2
    exact congrArg Prod.snd (E.map_sub u.1 v.1)
  have hae := Lp.ext_iff.mp hLp
  have hAE : gd.weakGradient =ᵐ[densityWeightedMeasure ρ] fun x =>
      gu.weakGradient x - gv.weakGradient x := by
    filter_upwards [hae, Lp.coeFn_sub
      (gu.gradient_memLp.toLp gu.weakGradient)
      (gv.gradient_memLp.toLp gv.weakGradient), gd.gradient_memLp.coeFn_toLp,
      gu.gradient_memLp.coeFn_toLp, gv.gradient_memLp.coeFn_toLp] with x heq hsub hd hu hv
    calc
      gd.weakGradient x = (gd.gradient_memLp.toLp gd.weakGradient) x := hd.symm
      _ = ((gu.gradient_memLp.toLp gu.weakGradient) -
        (gv.gradient_memLp.toLp gv.weakGradient)) x := heq
      _ = (gu.gradient_memLp.toLp gu.weakGradient) x -
        (gv.gradient_memLp.toLp gv.weakGradient) x := hsub
      _ = gu.weakGradient x - gv.weakGradient x := by rw [hu, hv]
  have hσ := (Measure.absolutelyContinuous_of_le_smul hMeasure).ae_eq hAE
  calc
    (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure (u - v)).weakGradient =ᵐ[
        densityWeightedMeasure σ] gd.weakGradient := Filter.Eventually.of_forall fun _ => rfl
    _ =ᵐ[densityWeightedMeasure σ] fun x => gu.weakGradient x - gv.weakGradient x := hσ
    _ =ᵐ[densityWeightedMeasure σ] fun x =>
        (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u).weakGradient x -
          (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure v).weakGradient x :=
      Filter.Eventually.of_forall fun _ => rfl

private theorem representativeValue_eq_spaceValue {d : ℕ} (ρ : Vec d → ℝ)
    (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    (u : densityWeightedH1Submodule ρ hρ hρpos) :
    (densityWeightedH1SpaceRepresentative ρ hρ hρpos u).value_memLp.toLp
      (densityWeightedH1SpaceRepresentative ρ hρ hρpos u).value =
      densityWeightedH1SpaceValue u := by
  have h := congrArg Prod.fst (densityWeightedH1SpaceRepresentative_pair u)
  change _ = _ at h
  exact h

private theorem sourcePhysicalGraph_value_add_ae {d : ℕ}
    (ρ : Vec d → ℝ) (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    (σ : Vec d → ℝ) (K : ℝ)
    (hMeasure : densityWeightedMeasure σ ≤
      ENNReal.ofReal K • densityWeightedMeasure ρ)
    (u v : densityWeightedH1Submodule ρ hρ hρpos) :
    (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure (u + v)).value =ᵐ[
      densityWeightedMeasure σ] fun x =>
        (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u).value x +
          (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure v).value x := by
  let gu := densityWeightedH1SpaceRepresentative ρ hρ hρpos u
  let gv := densityWeightedH1SpaceRepresentative ρ hρ hρpos v
  let gs := densityWeightedH1SpaceRepresentative ρ hρ hρpos (u + v)
  let E := WithLp.prodContinuousLinearEquiv 2 ℝ
    (Lp ℝ 2 (densityWeightedMeasure ρ))
    (Lp (EuclideanSpace ℝ (Fin d)) 2 (densityWeightedMeasure ρ))
  have hLp : gs.value_memLp.toLp gs.value =
      gu.value_memLp.toLp gu.value + gv.value_memLp.toLp gv.value := by
    rw [representativeValue_eq_spaceValue ρ hρ hρpos (u + v),
      representativeValue_eq_spaceValue ρ hρ hρpos u,
      representativeValue_eq_spaceValue ρ hρ hρpos v]
    change (E (u + v).1).1 = (E u.1).1 + (E v.1).1
    exact congrArg Prod.fst (E.map_add u.1 v.1)
  have hae := Lp.ext_iff.mp hLp
  have hAE : gs.value =ᵐ[densityWeightedMeasure ρ] fun x =>
      gu.value x + gv.value x := by
    filter_upwards [hae, Lp.coeFn_add
      (gu.value_memLp.toLp gu.value) (gv.value_memLp.toLp gv.value),
      gs.value_memLp.coeFn_toLp, gu.value_memLp.coeFn_toLp,
      gv.value_memLp.coeFn_toLp] with x heq hadd hs hu hv
    calc
      gs.value x = (gs.value_memLp.toLp gs.value) x := hs.symm
      _ = ((gu.value_memLp.toLp gu.value) + (gv.value_memLp.toLp gv.value)) x := heq
      _ = (gu.value_memLp.toLp gu.value) x + (gv.value_memLp.toLp gv.value) x := hadd
      _ = gu.value x + gv.value x := by rw [hu, hv]
  have hσ := (Measure.absolutelyContinuous_of_le_smul hMeasure).ae_eq hAE
  calc
    (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure (u + v)).value =ᵐ[
        densityWeightedMeasure σ] gs.value := Filter.Eventually.of_forall fun _ => rfl
    _ =ᵐ[densityWeightedMeasure σ] fun x => gu.value x + gv.value x := hσ
    _ =ᵐ[densityWeightedMeasure σ] fun x =>
        (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u).value x +
          (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure v).value x :=
      Filter.Eventually.of_forall fun _ => rfl

private theorem sourcePhysicalGraph_value_sub_ae {d : ℕ}
    (ρ : Vec d → ℝ) (hρ : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    (σ : Vec d → ℝ) (K : ℝ)
    (hMeasure : densityWeightedMeasure σ ≤
      ENNReal.ofReal K • densityWeightedMeasure ρ)
    (u v : densityWeightedH1Submodule ρ hρ hρpos) :
    (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure (u - v)).value =ᵐ[
      densityWeightedMeasure σ] fun x =>
        (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u).value x -
          (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure v).value x := by
  let gu := densityWeightedH1SpaceRepresentative ρ hρ hρpos u
  let gv := densityWeightedH1SpaceRepresentative ρ hρ hρpos v
  let gd := densityWeightedH1SpaceRepresentative ρ hρ hρpos (u - v)
  let E := WithLp.prodContinuousLinearEquiv 2 ℝ
    (Lp ℝ 2 (densityWeightedMeasure ρ))
    (Lp (EuclideanSpace ℝ (Fin d)) 2 (densityWeightedMeasure ρ))
  have hLp : gd.value_memLp.toLp gd.value =
      gu.value_memLp.toLp gu.value - gv.value_memLp.toLp gv.value := by
    rw [representativeValue_eq_spaceValue ρ hρ hρpos (u - v),
      representativeValue_eq_spaceValue ρ hρ hρpos u,
      representativeValue_eq_spaceValue ρ hρ hρpos v]
    change (E (u - v).1).1 = (E u.1).1 - (E v.1).1
    exact congrArg Prod.fst (E.map_sub u.1 v.1)
  have hae := Lp.ext_iff.mp hLp
  have hAE : gd.value =ᵐ[densityWeightedMeasure ρ] fun x =>
      gu.value x - gv.value x := by
    filter_upwards [hae, Lp.coeFn_sub
      (gu.value_memLp.toLp gu.value) (gv.value_memLp.toLp gv.value),
      gd.value_memLp.coeFn_toLp, gu.value_memLp.coeFn_toLp,
      gv.value_memLp.coeFn_toLp] with x heq hsub hd hu hv
    calc
      gd.value x = (gd.value_memLp.toLp gd.value) x := hd.symm
      _ = ((gu.value_memLp.toLp gu.value) - (gv.value_memLp.toLp gv.value)) x := heq
      _ = (gu.value_memLp.toLp gu.value) x - (gv.value_memLp.toLp gv.value) x := hsub
      _ = gu.value x - gv.value x := by rw [hu, hv]
  have hσ := (Measure.absolutelyContinuous_of_le_smul hMeasure).ae_eq hAE
  calc
    (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure (u - v)).value =ᵐ[
        densityWeightedMeasure σ] gd.value := Filter.Eventually.of_forall fun _ => rfl
    _ =ᵐ[densityWeightedMeasure σ] fun x => gu.value x - gv.value x := hσ
    _ =ᵐ[densityWeightedMeasure σ] fun x =>
        (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u).value x -
          (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure v).value x :=
      Filter.Eventually.of_forall fun _ => rfl

private theorem sourcePhysicalGraph_quotientValue_ae {d : ℕ}
    (ω : FieldPair d) (hd : 2 ≤ d) (lam L : ℝ)
    (hω : IsRegular L ω)
    (z : densityWeightedH1Submodule (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)) :
    densityWeightedH1Value (sourceReducedDensity hd lam)
        ((densityWeightedH1GraphEquiv (sourceReducedDensity hd lam)
          (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)).symm z) =ᵐ[
      densityWeightedMeasure (sourcePhysicalDensity ω hd lam)]
      (sourcePhysicalGraph (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
        (sourcePhysicalDensity ω hd lam) (Real.exp (2 * L))
        (sourcePhysicalMeasure_le_reduced ω hd lam L hω) z).value := by
  let ρ := sourceReducedDensity hd lam
  let E := densityWeightedH1GraphEquiv ρ
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
  let q := E.symm z
  let g := densityWeightedH1SpaceRepresentative ρ
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) z
  have hEq : E q = z := E.apply_symm_apply z
  have hp := physicalH1Representative_pair_eq_quotient_pair
    hd lam q
  have hLp : g.value_memLp.toLp g.value = densityWeightedH1Value ρ q := by
    change (densityWeightedH1SpaceRepresentative ρ
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) z).value_memLp.toLp
        (densityWeightedH1SpaceRepresentative ρ
          (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) z).value =
      densityWeightedH1Value ρ q
    rw [← hEq]
    exact congrArg Prod.fst hp
  have hAE : densityWeightedH1Value ρ q =ᵐ[densityWeightedMeasure ρ] g.value := by
    filter_upwards [Lp.ext_iff.mp hLp.symm, g.value_memLp.coeFn_toLp] with x heq hg
    exact heq.trans hg
  have hMeasure : densityWeightedMeasure (sourcePhysicalDensity ω hd lam) ≤
      ENNReal.ofReal (Real.exp (2 * L)) • densityWeightedMeasure ρ :=
    sourcePhysicalMeasure_le_reduced ω hd lam L hω
  have hσ := (Measure.absolutelyContinuous_of_le_smul hMeasure).ae_eq hAE
  change densityWeightedH1Value ρ q =ᵐ[densityWeightedMeasure (sourcePhysicalDensity ω hd lam)]
    (densityWeightedH1SpaceRepresentative ρ
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) z).value at hσ
  change densityWeightedH1Value (sourceReducedDensity hd lam)
      ((densityWeightedH1GraphEquiv (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)).symm z) =ᵐ[
      densityWeightedMeasure (sourcePhysicalDensity ω hd lam)]
    (sourcePhysicalGraph (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
      (sourcePhysicalDensity ω hd lam) (Real.exp (2 * L))
      (sourcePhysicalMeasure_le_reduced ω hd lam L hω) z).value
  exact hσ

/-- The physical Dirichlet form on two arbitrary full force-weighted H¹ elements is the
real polarization of its diagonal values. -/
private theorem sourcePhysicalDirichletForm_polarization {d : ℕ}
    (ω : FieldPair d) (hd : 2 ≤ d) (lam L : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω)
    (u v : densityWeightedH1Submodule (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)) :
    sourcePhysicalDirichletForm (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
        (sourcePhysicalDensity ω hd lam) (Real.exp (2 * L))
        (sourcePhysicalMeasure_le_reduced ω hd lam L hω) ω.1 u v =
      (1 / 4 : ℝ) * (
        sourcePhysicalDirichletForm (sourceReducedDensity hd lam)
          (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
          (sourcePhysicalDensity ω hd lam) (Real.exp (2 * L))
          (sourcePhysicalMeasure_le_reduced ω hd lam L hω) ω.1 (u + v) (u + v) -
        sourcePhysicalDirichletForm (sourceReducedDensity hd lam)
          (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
          (sourcePhysicalDensity ω hd lam) (Real.exp (2 * L))
          (sourcePhysicalMeasure_le_reduced ω hd lam L hω) ω.1 (u - v) (u - v)) := by
  let ρ := sourceReducedDensity hd lam
  let σ := sourcePhysicalDensity ω hd lam
  let K := Real.exp (2 * L)
  let hρ : Continuous ρ := continuousSourceReducedDensity hd lam
  let hρpos : ∀ x, 0 < ρ x := positiveSourceReducedDensity hd lam
  let hMeasure : densityWeightedMeasure σ ≤
      ENNReal.ofReal K • densityWeightedMeasure ρ := by
    dsimp [σ, ρ, K]
    exact sourcePhysicalMeasure_le_reduced ω hd lam L hω
  let gu := sourcePhysicalGraph ρ hρ hρpos σ K hMeasure u
  let gv := sourcePhysicalGraph ρ hρ hρpos σ K hMeasure v
  let gp := sourcePhysicalGraph ρ hρ hρpos σ K hMeasure (u + v)
  let gm := sourcePhysicalGraph ρ hρ hρpos σ K hMeasure (u - v)
  have hpoint : weightedFormIntegrand ω.1 gp gp - weightedFormIntegrand ω.1 gm gm =ᵐ[
      densityWeightedMeasure σ] fun x => 4 * weightedFormIntegrand ω.1 gu gv x := by
    filter_upwards [sourcePhysicalGraph_gradient_add_ae ρ hρ hρpos σ K hMeasure u v,
      sourcePhysicalGraph_gradient_sub_ae ρ hρ hρpos σ K hMeasure u v] with x hp hm
    change gp.weakGradient x = gu.weakGradient x + gv.weakGradient x at hp
    change gm.weakGradient x = gu.weakGradient x - gv.weakGradient x at hm
    change (1 / 2 : ℝ) * dot (WithLp.ofLp (gp.weakGradient x))
        ((ω.1 x).mulVec (WithLp.ofLp (gp.weakGradient x))) -
      (1 / 2 : ℝ) * dot (WithLp.ofLp (gm.weakGradient x))
        ((ω.1 x).mulVec (WithLp.ofLp (gm.weakGradient x))) =
      4 * ((1 / 2 : ℝ) * dot (WithLp.ofLp (gu.weakGradient x))
        ((ω.1 x).mulVec (WithLp.ofLp (gv.weakGradient x))))
    have hsym := hω.1 x |>.1
    rw [hp, hm, WithLp.ofLp_add, WithLp.ofLp_sub]
    have hquad := sourceDot_mulVec_quadratic_polarization (ω.1 x) hsym
      (WithLp.ofLp (gu.weakGradient x)) (WithLp.ofLp (gv.weakGradient x))
    linear_combination (1 / 2 : ℝ) * hquad
  have hiU := physicalWeightedFormIntegrand_integrable_of_regular ω L hL hω gp gp
  have hiV := physicalWeightedFormIntegrand_integrable_of_regular ω L hL hω gm gm
  have hInt := integral_congr_ae hpoint
  have hPolar :
      sourcePhysicalDirichletForm ρ hρ hρpos σ K hMeasure ω.1 u v * 4 =
        sourcePhysicalDirichletForm ρ hρ hρpos σ K hMeasure ω.1 (u + v) (u + v) -
          sourcePhysicalDirichletForm ρ hρ hρpos σ K hMeasure ω.1 (u - v) (u - v) := by
    change (∫ x, weightedFormIntegrand ω.1 gu gv x ∂densityWeightedMeasure σ) * 4 =
      (∫ x, weightedFormIntegrand ω.1 gp gp x ∂densityWeightedMeasure σ) -
        ∫ x, weightedFormIntegrand ω.1 gm gm x ∂densityWeightedMeasure σ
    calc
      _ = 4 * ∫ x, weightedFormIntegrand ω.1 gu gv x ∂densityWeightedMeasure σ := by ring
      _ = ∫ x, (4 * weightedFormIntegrand ω.1 gu gv x) ∂densityWeightedMeasure σ :=
        (integral_const_mul 4 _).symm
      _ = ∫ x, (weightedFormIntegrand ω.1 gp gp - weightedFormIntegrand ω.1 gm gm) x
          ∂densityWeightedMeasure σ := hInt.symm
      _ = _ := integral_sub hiU hiV
  nlinarith [hPolar]

/-- The mixed physical form is the polarization of the canonical full-H¹ energy on the
quotient representatives of `u + v` and `u - v`. -/
private theorem sourcePhysicalDirichletForm_eq_physicalH1FormEnergy_polarization {d : ℕ}
    (ω : FieldPair d) (hd : 2 ≤ d) (lam L : ℝ)
    (hL : 1 ≤ L) (hω : IsRegular L ω)
    (u v : densityWeightedH1Submodule (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)) :
    sourcePhysicalDirichletForm (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
        (sourcePhysicalDensity ω hd lam) (Real.exp (2 * L))
        (sourcePhysicalMeasure_le_reduced ω hd lam L hω) ω.1 u v =
      (1 / 4 : ℝ) * (
        External.GantertSection7Support.physicalH1FormEnergy ω hd lam
          (densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
            (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
            (u + v)) -
        External.GantertSection7Support.physicalH1FormEnergy ω hd lam
          (densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
            (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
            (u - v))) := by
  rw [sourcePhysicalDirichletForm_polarization ω hd lam L hL hω u v,
    sourcePhysicalDirichletForm_self_eq_physicalH1FormEnergy ω hd lam L hω (u + v),
    sourcePhysicalDirichletForm_self_eq_physicalH1FormEnergy ω hd lam L hω (u - v)]

/-- The quotient H¹ value of `u + v` is represented by the sum of the corresponding actual
physical L² values. -/
private theorem sourcePhysicalGraph_quotientValue_add_ae {d : ℕ}
    (ω : FieldPair d) (hd : 2 ≤ d) (lam L : ℝ) (hω : IsRegular L ω)
    (u v : densityWeightedH1Submodule (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)) :
    densityWeightedH1Value (sourceReducedDensity hd lam)
        ((densityWeightedH1GraphEquiv (sourceReducedDensity hd lam)
          (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)).symm
          (u + v)) =ᵐ[densityWeightedMeasure (sourcePhysicalDensity ω hd lam)]
      fun x =>
        (densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
          (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) u).value x +
        (densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
          (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) v).value x := by
  let ρ := sourceReducedDensity hd lam
  let σ := sourcePhysicalDensity ω hd lam
  let K := Real.exp (2 * L)
  let hρ : Continuous ρ := continuousSourceReducedDensity hd lam
  let hρpos : ∀ x, 0 < ρ x := positiveSourceReducedDensity hd lam
  let hMeasure : densityWeightedMeasure σ ≤
      ENNReal.ofReal K • densityWeightedMeasure ρ := by
    dsimp [σ, ρ, K]
    exact sourcePhysicalMeasure_le_reduced ω hd lam L hω
  have hq := sourcePhysicalGraph_quotientValue_ae ω hd lam L hω (u + v)
  have hsum := sourcePhysicalGraph_value_add_ae ρ hρ hρpos σ K hMeasure u v
  change densityWeightedH1Value ρ
      ((densityWeightedH1GraphEquiv ρ hρ hρpos).symm (u + v)) =ᵐ[
        densityWeightedMeasure σ]
    (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure (u + v)).value at hq
  change (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure (u + v)).value =ᵐ[
    densityWeightedMeasure σ] _ at hsum
  exact hq.trans hsum

/-- The quotient H¹ value of `u - v` is represented by the difference of the corresponding
actual physical L² values. -/
private theorem sourcePhysicalGraph_quotientValue_sub_ae {d : ℕ}
    (ω : FieldPair d) (hd : 2 ≤ d) (lam L : ℝ) (hω : IsRegular L ω)
    (u v : densityWeightedH1Submodule (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)) :
    densityWeightedH1Value (sourceReducedDensity hd lam)
        ((densityWeightedH1GraphEquiv (sourceReducedDensity hd lam)
          (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)).symm
          (u - v)) =ᵐ[densityWeightedMeasure (sourcePhysicalDensity ω hd lam)]
      fun x =>
        (densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
          (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) u).value x -
        (densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
          (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) v).value x := by
  let ρ := sourceReducedDensity hd lam
  let σ := sourcePhysicalDensity ω hd lam
  let K := Real.exp (2 * L)
  let hρ : Continuous ρ := continuousSourceReducedDensity hd lam
  let hρpos : ∀ x, 0 < ρ x := positiveSourceReducedDensity hd lam
  let hMeasure : densityWeightedMeasure σ ≤
      ENNReal.ofReal K • densityWeightedMeasure ρ := by
    dsimp [σ, ρ, K]
    exact sourcePhysicalMeasure_le_reduced ω hd lam L hω
  have hq := sourcePhysicalGraph_quotientValue_ae ω hd lam L hω (u - v)
  have hsub := sourcePhysicalGraph_value_sub_ae ρ hρ hρpos σ K hMeasure u v
  change densityWeightedH1Value ρ
      ((densityWeightedH1GraphEquiv ρ hρ hρpos).symm (u - v)) =ᵐ[
        densityWeightedMeasure σ]
    (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure (u - v)).value at hq
  change (sourcePhysicalGraph ρ hρ hρpos σ K hMeasure (u - v)).value =ᵐ[
    densityWeightedMeasure σ] _ at hsub
  exact hq.trans hsub

/-- The two actual physical L² test functions induced by a pair of full force-weighted H¹
elements. -/
private def physicalH1PolarizationValuePair {d : ℕ} (hd : 2 ≤ d) (lam : ℝ)
    (u v : densityWeightedH1Submodule (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)) :
    (Vec d → ℝ) × (Vec d → ℝ) :=
  let gu := densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) u
  let gv := densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) v
  (fun x => gu.value x + gv.value x, fun x => gu.value x - gv.value x)

/-- The polarization of the closed-form difference quotient on the two actual physical L²
representatives carried by the full weighted H¹ graph. -/
private def physicalSemigroupFormPolarizationDifferenceQuotient {d : ℕ}
    (ω : FieldPair d) (hd : 2 ≤ d) (lam : ℝ)
    (K : ℝ≥0 → Kernel (Vec d) (Vec d))
    (u v : densityWeightedH1Submodule (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam))
    (t : ℝ≥0) : ℝ :=
  let F := physicalH1PolarizationValuePair hd lam u v
  (1 / 4 : ℝ) * (
    External.GantertSection7Support.semigroupFormDifferenceQuotient ω hd lam K t
      F.1 -
    External.GantertSection7Support.semigroupFormDifferenceQuotient ω hd lam K t
      F.2)

private theorem givenRealization_semigroupForm_tendsto_closedForm {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (ω : FieldPair d)
    (hω : IsRegular Λ₀ ω) (lam : ℝ) (hlam : 0 ≤ lam) (hlam_le_one : lam ≤ 1)
    (R : External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd Λ₀ hΛ₀ ω hω lam hlam hlam_le_one)
    (f : Vec d → ℝ)
    (q : DensityWeightedH1 (External.GantertSection7Support.physicalForceWeight hd lam))
    (hq : densityWeightedH1Value (External.GantertSection7Support.physicalForceWeight hd lam) q =ᵐ[
      External.GantertSection7Support.physicalReversibleMeasure ω hd lam] f)
    (g : WeightedSobolevGraph (External.GantertSection7Support.physicalForceMeasure hd lam))
    (hg : g.value =ᵐ[
      External.GantertSection7Support.physicalReversibleMeasure ω hd lam] f) :
    Tendsto
      (fun t => External.GantertSection7Support.semigroupFormDifferenceQuotient
        ω hd lam R.transitionKernel t f)
      (𝓝[Set.Ioi 0] (0 : ℝ≥0))
      (𝓝 (External.GantertSection7Support.physicalH1FormEnergy ω hd lam g)) :=
  R.closedForm_value f q hq g hg

private theorem physicalH1Polarization_closedFormInputs {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ : ℝ} (ω : FieldPair d) (hω : IsRegular Λ₀ ω)
    (lam : ℝ)
    (u v : densityWeightedH1Submodule (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)) :
    (densityWeightedH1Value (sourceReducedDensity hd lam)
        ((densityWeightedH1GraphEquiv (sourceReducedDensity hd lam)
          (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)).symm
          (u + v)) =ᵐ[densityWeightedMeasure (sourcePhysicalDensity ω hd lam)]
          (physicalH1PolarizationValuePair hd lam u v).1 ∧
      (densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) (u + v)).value =ᵐ[
          densityWeightedMeasure (sourcePhysicalDensity ω hd lam)]
          (physicalH1PolarizationValuePair hd lam u v).1) ∧
    (densityWeightedH1Value (sourceReducedDensity hd lam)
        ((densityWeightedH1GraphEquiv (sourceReducedDensity hd lam)
          (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)).symm
          (u - v)) =ᵐ[densityWeightedMeasure (sourcePhysicalDensity ω hd lam)]
          (physicalH1PolarizationValuePair hd lam u v).2 ∧
      (densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) (u - v)).value =ᵐ[
          densityWeightedMeasure (sourcePhysicalDensity ω hd lam)]
          (physicalH1PolarizationValuePair hd lam u v).2) := by
  let ρ := sourceReducedDensity hd lam
  let σ := sourcePhysicalDensity ω hd lam
  let K := Real.exp (2 * Λ₀)
  let hρ : Continuous ρ := continuousSourceReducedDensity hd lam
  let hρpos : ∀ x, 0 < ρ x := positiveSourceReducedDensity hd lam
  let hMeasure : densityWeightedMeasure σ ≤
      ENNReal.ofReal K • densityWeightedMeasure ρ := by
    dsimp [σ, ρ, K]
    exact sourcePhysicalMeasure_le_reduced ω hd lam Λ₀ hω
  have hqplus := sourcePhysicalGraph_quotientValue_add_ae ω hd lam Λ₀ hω u v
  have hqminus := sourcePhysicalGraph_quotientValue_sub_ae ω hd lam Λ₀ hω u v
  have hgplus : (densityWeightedH1SpaceRepresentative ρ
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) (u + v)).value =ᵐ[
        densityWeightedMeasure σ] (physicalH1PolarizationValuePair hd lam u v).1 := by
    have hsum := sourcePhysicalGraph_value_add_ae ρ hρ hρpos σ K hMeasure u v
    change (densityWeightedH1SpaceRepresentative ρ
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) (u + v)).value =ᵐ[
        densityWeightedMeasure σ] (physicalH1PolarizationValuePair hd lam u v).1
    exact hsum
  have hgminus : (densityWeightedH1SpaceRepresentative ρ
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) (u - v)).value =ᵐ[
        densityWeightedMeasure σ] (physicalH1PolarizationValuePair hd lam u v).2 := by
    have hsub := sourcePhysicalGraph_value_sub_ae ρ hρ hρpos σ K hMeasure u v
    change (densityWeightedH1SpaceRepresentative ρ
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) (u - v)).value =ᵐ[
        densityWeightedMeasure σ] (physicalH1PolarizationValuePair hd lam u v).2
    exact hsub
  exact ⟨⟨hqplus, hgplus⟩, ⟨hqminus, hgminus⟩⟩

private theorem givenRealization_semigroupForm_tendsto_add {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (ω : FieldPair d)
    (hω : IsRegular Λ₀ ω) (lam : ℝ) (hlam : 0 ≤ lam) (hlam_le_one : lam ≤ 1)
    (R : External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd Λ₀ hΛ₀ ω hω lam hlam hlam_le_one)
    (u v : densityWeightedH1Submodule (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)) :
    Tendsto
      (fun t => External.GantertSection7Support.semigroupFormDifferenceQuotient
        ω hd lam R.transitionKernel t (physicalH1PolarizationValuePair hd lam u v).1)
      (𝓝[Set.Ioi 0] (0 : ℝ≥0))
      (𝓝 (External.GantertSection7Support.physicalH1FormEnergy ω hd lam
        (densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
          (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) (u + v)))) := by
  let F := physicalH1PolarizationValuePair hd lam u v
  let q := densityWeightedH1GraphEquiv (sourceReducedDensity hd lam)
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) |>.symm (u + v)
  let g := densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) (u + v)
  have hinput := physicalH1Polarization_closedFormInputs hd ω hω lam u v
  exact givenRealization_semigroupForm_tendsto_closedForm
    hd hΛ₀ ω hω lam hlam hlam_le_one R F.1 q hinput.1.1 g hinput.1.2

private theorem givenRealization_semigroupForm_tendsto_sub {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (ω : FieldPair d)
    (hω : IsRegular Λ₀ ω) (lam : ℝ) (hlam : 0 ≤ lam) (hlam_le_one : lam ≤ 1)
    (R : External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd Λ₀ hΛ₀ ω hω lam hlam hlam_le_one)
    (u v : densityWeightedH1Submodule (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)) :
    Tendsto
      (fun t => External.GantertSection7Support.semigroupFormDifferenceQuotient
        ω hd lam R.transitionKernel t (physicalH1PolarizationValuePair hd lam u v).2)
      (𝓝[Set.Ioi 0] (0 : ℝ≥0))
      (𝓝 (External.GantertSection7Support.physicalH1FormEnergy ω hd lam
        (densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
          (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) (u - v)))) := by
  let F := physicalH1PolarizationValuePair hd lam u v
  let q := densityWeightedH1GraphEquiv (sourceReducedDensity hd lam)
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) |>.symm (u - v)
  let g := densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) (u - v)
  have hinput := physicalH1Polarization_closedFormInputs hd ω hω lam u v
  exact givenRealization_semigroupForm_tendsto_closedForm
    hd hΛ₀ ω hω lam hlam hlam_le_one R F.2 q hinput.2.1 g hinput.2.2

private theorem givenRealization_physicalSemigroupFormPolarization_tendsto_energy {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (ω : FieldPair d)
    (hω : IsRegular Λ₀ ω) (lam : ℝ) (hlam : 0 ≤ lam) (hlam_le_one : lam ≤ 1)
    (R : External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd Λ₀ hΛ₀ ω hω lam hlam hlam_le_one)
    (u v : densityWeightedH1Submodule (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)) :
    Tendsto
      (fun t => physicalSemigroupFormPolarizationDifferenceQuotient
        ω hd lam R.transitionKernel u v t)
      (𝓝[Set.Ioi 0] (0 : ℝ≥0))
      (𝓝 ((1 / 4 : ℝ) * (
        External.GantertSection7Support.physicalH1FormEnergy ω hd lam
          (densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
            (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) (u + v)) -
        External.GantertSection7Support.physicalH1FormEnergy ω hd lam
          (densityWeightedH1SpaceRepresentative (sourceReducedDensity hd lam)
            (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) (u - v))))) := by
  let F := physicalH1PolarizationValuePair hd lam u v
  have hplus := givenRealization_semigroupForm_tendsto_add
    hd hΛ₀ ω hω lam hlam hlam_le_one R u v
  have hminus := givenRealization_semigroupForm_tendsto_sub
    hd hΛ₀ ω hω lam hlam hlam_le_one R u v
  have hscaled := (hplus.sub hminus).const_mul (1 / 4 : ℝ)
  have hfun :
      (fun t => physicalSemigroupFormPolarizationDifferenceQuotient
        ω hd lam R.transitionKernel u v t) =
      (fun t : ℝ≥0 => (1 / 4 : ℝ) * (
        External.GantertSection7Support.semigroupFormDifferenceQuotient
          ω hd lam R.transitionKernel t F.1 -
        External.GantertSection7Support.semigroupFormDifferenceQuotient
          ω hd lam R.transitionKernel t F.2)) := by
    funext t
    rfl
  rw [hfun]
  exact hscaled

/-- The closed-form difference quotient polarized on two arbitrary elements of the full
force-weighted H¹ graph converges to the mixed physical Dirichlet form. -/
private theorem givenRealization_physicalSemigroupFormPolarization_tendsto {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ : ℝ} (hΛ₀ : 1 ≤ Λ₀) (ω : FieldPair d)
    (hω : IsRegular Λ₀ ω) (lam : ℝ) (hlam : 0 ≤ lam) (hlam_le_one : lam ≤ 1)
    (R : External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd Λ₀ hΛ₀ ω hω lam hlam hlam_le_one)
    (u v : densityWeightedH1Submodule (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)) :
    Tendsto
      (fun t => physicalSemigroupFormPolarizationDifferenceQuotient
        ω hd lam R.transitionKernel u v t)
      (𝓝[Set.Ioi 0] (0 : ℝ≥0))
      (𝓝 (sourcePhysicalDirichletForm (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
        (sourcePhysicalDensity ω hd lam) (Real.exp (2 * Λ₀))
        (sourcePhysicalMeasure_le_reduced ω hd lam Λ₀ hω) ω.1 u v)) := by
  have hpolar := givenRealization_physicalSemigroupFormPolarization_tendsto_energy
    hd hΛ₀ ω hω lam hlam hlam_le_one R u v
  rw [sourcePhysicalDirichletForm_eq_physicalH1FormEnergy_polarization
    ω hd lam Λ₀ hΛ₀ hω u v]
  exact hpolar


private theorem formQuotient_congr {d : ℕ} (hd : 2 ≤ d)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) {ω : FieldPair d} {hω : IsRegular Λ ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (R : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (t : ℝ≥0) {f g : Vec d → ℝ}
    (hfg : f =ᵐ[physicalReversibleMeasure ω hd lam] g) :
    semigroupFormDifferenceQuotient ω hd lam R.transitionKernel t f =
      semigroupFormDifferenceQuotient ω hd lam R.transitionKernel t g := by
  letI : ProbabilityTheory.IsMarkovKernel (R.transitionKernel t) :=
    R.transitionKernel_isMarkovKernel t
  have hk := WeightedKernelL2.kernelIntegral_ae_congr
    (R.transitionKernel_invariant hd hΛ t) hfg
  unfold semigroupFormDifferenceQuotient
  congr 1
  apply integral_congr_ae
  filter_upwards [hfg, hk] with x hx hy
  change (f x - WeightedKernelL2.kernelIntegral (R.transitionKernel t) f x) * f x = _
  rw [hx, hy]
  rfl

private theorem actual_mixed_quotient_limit {d : ℕ} (hd : 2 ≤ d)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) {ω : FieldPair d} {hω : IsRegular Λ ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (R : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (u v : densityWeightedH1Submodule (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)) :
    let U : Lp ℝ 2 (physicalReversibleMeasure ω hd lam) := sourcePhysicalValue (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
        (sourcePhysicalDensity ω hd lam) (Real.exp (2 * Λ))
        (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω) u
    let V : Lp ℝ 2 (physicalReversibleMeasure ω hd lam) := sourcePhysicalValue (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
        (sourcePhysicalDensity ω hd lam) (Real.exp (2 * Λ))
        (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω) v
    Tendsto (fun t : ℝ≥0 => (1 / (t : ℝ)) * inner ℝ
      (U - R.kernelL2Action hd hΛ t U) V)
      (𝓝[Set.Ioi 0] (0 : ℝ≥0))
      (𝓝 (sourcePhysicalDirichletForm (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
        (sourcePhysicalDensity ω hd lam) (Real.exp (2 * Λ))
        (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω) ω.1 u v)) := by
  let ρ := sourceReducedDensity hd lam
  let σ := sourcePhysicalDensity ω hd lam
  let K := Real.exp (2 * Λ)
  let hρ := continuousSourceReducedDensity hd lam
  let hpos := positiveSourceReducedDensity hd lam
  let hm := sourcePhysicalMeasure_le_reduced ω hd lam Λ hω
  let gu := sourcePhysicalGraph ρ hρ hpos σ K hm u
  let gv := sourcePhysicalGraph ρ hρ hpos σ K hm v
  let U : Lp ℝ 2 (physicalReversibleMeasure ω hd lam) :=
    sourcePhysicalValue ρ hρ hpos σ K hm u
  let V : Lp ℝ 2 (physicalReversibleMeasure ω hd lam) :=
    sourcePhysicalValue ρ hρ hpos σ K hm v
  have hU : (U : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] gu.value :=
    gu.value_memLp.coeFn_toLp
  have hV : (V : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] gv.value :=
    gv.value_memLp.coeFn_toLp
  have hplus : (physicalH1PolarizationValuePair hd lam u v).1 =ᵐ[
      physicalReversibleMeasure ω hd lam] (U + V : Lp ℝ 2 _) := by
    filter_upwards [hU, hV, Lp.coeFn_add U V] with x hu hv ha
    change gu.value x + gv.value x = _
    rw [ha]
    change _ = U x + V x
    rw [hu, hv]
  have hminus : (physicalH1PolarizationValuePair hd lam u v).2 =ᵐ[
      physicalReversibleMeasure ω hd lam] (U - V : Lp ℝ 2 _) := by
    filter_upwards [hU, hV, Lp.coeFn_sub U V] with x hu hv ha
    change gu.value x - gv.value x = _
    rw [ha]
    change _ = U x - V x
    rw [hu, hv]
  have hlim := givenRealization_physicalSemigroupFormPolarization_tendsto
    hd hΛ ω hω lam h0 h1 R u v
  apply hlim.congr'
  apply Filter.Eventually.of_forall
  intro t
  change physicalSemigroupFormPolarizationDifferenceQuotient
    ω hd lam R.transitionKernel u v t = (1 / (t : ℝ)) * inner ℝ
      (U - R.kernelL2Action hd hΛ t U) V
  unfold physicalSemigroupFormPolarizationDifferenceQuotient
  dsimp only
  rw [formQuotient_congr hd hΛ R t hplus,
    formQuotient_congr hd hΛ R t hminus,
    semigroupFormDifferenceQuotient_eq_inner hd hΛ R,
    semigroupFormDifferenceQuotient_eq_inner hd hΛ R]
  have hadd : R.kernelL2Action hd hΛ t (U + V) =
      R.kernelL2Action hd hΛ t U + R.kernelL2Action hd hΛ t V := by
    have h := R.kernelL2Action_sub hd hΛ t (U + V) V
    rw [add_sub_cancel_right] at h
    exact eq_add_of_sub_eq h.symm
  rw [hadd, R.kernelL2Action_sub hd hΛ t]
  simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right]
  have hcross : inner ℝ (R.kernelL2Action hd hΛ t V) U =
      inner ℝ (R.kernelL2Action hd hΛ t U) V := by
    rw [← kernelL2Action_symmetric hd hΛ R t V U, real_inner_comm]
  rw [real_inner_comm V U, hcross]
  ring

private theorem compact_mixed_quotient_limit {d : ℕ} (hd : 2 ≤ d)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) {ω : FieldPair d} {hω : IsRegular Λ ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (R : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (hSmooth : IsSmoothFieldPair ω)
    (u : densityWeightedH1Submodule (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam))
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (f0 : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hrep : (f0 : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] f) :
    let U : Lp ℝ 2 (physicalReversibleMeasure ω hd lam) := sourcePhysicalValue (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
        (sourcePhysicalDensity ω hd lam) (Real.exp (2 * Λ))
        (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω) u
    Tendsto (fun t : ℝ≥0 => (1 / (t : ℝ)) * inner ℝ
      (U - R.kernelL2Action hd hΛ t U) f0)
      (𝓝[Set.Ioi 0] (0 : ℝ≥0))
      (𝓝 (-inner ℝ (sourcePhysicalValue (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
        (sourcePhysicalDensity ω hd lam) (Real.exp (2 * Λ))
        (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω) u)
        (compactTestGeneratorL2 hd ω hSmooth lam f hf hc))) := by
  let v := compactTestDomain hd lam f hf hc
  have hv : sourcePhysicalValue (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
      (sourcePhysicalDensity ω hd lam) (Real.exp (2 * Λ))
      (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω) v = f0 := by
    apply Lp.ext
    exact ((sourcePhysicalGraph (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
      (sourcePhysicalDensity ω hd lam) (Real.exp (2 * Λ))
      (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω) v).value_memLp.coeFn_toLp.trans
        (compactTestDomain_value hd Λ ω hω lam f hf hc)).trans hrep.symm
  have hlim := actual_mixed_quotient_limit hd hΛ R u v
  rw [hv] at hlim
  rw [compactTest_fullDomain_generatorInner hd Λ ω hω lam hSmooth u f hf hc] at hlim
  exact hlim

private theorem compact_action_tendsto_zero {d : ℕ} (hd : 2 ≤ d)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) {ω : FieldPair d} {hω : IsRegular Λ ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (R : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (f0 : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hrep : (f0 : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] f) :
    Tendsto (fun t : ℝ≥0 => R.kernelL2Action hd hΛ t f0)
      (𝓝[Set.Ioi 0] (0 : ℝ≥0)) (𝓝 f0) := by
  let fm : MemLp f 2 (physicalReversibleMeasure ω hd lam) := (memLp_congr_ae hrep).mp (Lp.memLp f0)
  obtain ⟨q, hq⟩ := compactTest_mem_physicalH1 hd Λ ω hω lam f hf hc
  have hlim := R.kernelL2Action_tendsto_fullPhysicalH1 hd hΛ ω hω lam h0 h1
    f fm q hq (compactTestGraph hd lam f hf hc) (EventuallyEq.rfl)
  have he : fm.toLp f = f0 := by
    apply Lp.ext
    exact fm.coeFn_toLp.trans hrep.symm
  rw [he] at hlim
  exact hlim

/- Local finite-on-compacts helper from PhysicalH1DensitySupport; the latter
module has an unrelated integration-by-parts API failure under Lean 4.35. -/
private theorem finiteOnCompacts_of_locallyFinite {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] {m : Measure X} [IsLocallyFiniteMeasure m] :
    IsFiniteMeasureOnCompacts m := by
  refine ⟨?_⟩
  intro K hK
  let U : K → Set X := fun x => Classical.choose (m.exists_isOpen_measure_lt_top x.1)
  have hU : ∀ x : K, (x : X) ∈ U x ∧ IsOpen (U x) ∧ m (U x) < ∞ := by
    intro x
    exact Classical.choose_spec (m.exists_isOpen_measure_lt_top x.1)
  have hcover : K ⊆ ⋃ x : K, U x := by
    intro x hx
    exact Set.mem_iUnion.2 ⟨⟨x, hx⟩, (hU ⟨x, hx⟩).1⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U (fun x => (hU x).2.1) hcover
  calc
    m K ≤ m (⋃ x ∈ t, U x) := measure_mono ht
    _ ≤ ∑ x ∈ t, m (U x) := measure_biUnion_finset_le t U
    _ < ∞ := ENNReal.sum_lt_top.mpr (fun x hx => (hU x).2.2)

private def actualActionCLM {d : ℕ} (hd : 2 ≤ d)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) {ω : FieldPair d} {hω : IsRegular Λ ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (R : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (t : ℝ≥0) :
    Lp ℝ 2 (physicalReversibleMeasure ω hd lam) →L[ℝ]
      Lp ℝ 2 (physicalReversibleMeasure ω hd lam) :=
  LinearMap.mkContinuous
    { toFun := R.kernelL2Action hd hΛ t
      map_add' := fun f g => by
        apply ext_inner_right ℝ
        intro u
        rw [← kernelL2Action_symmetric hd hΛ R, inner_add_left,
          inner_add_left, ← kernelL2Action_symmetric hd hΛ R,
          ← kernelL2Action_symmetric hd hΛ R]
      map_smul' := fun c f => by
        apply ext_inner_right ℝ
        intro u
        rw [← kernelL2Action_symmetric hd hΛ R, inner_smul_left,
          inner_smul_left, ← kernelL2Action_symmetric hd hΛ R]
        simp }
    1 (fun f => by
      change ‖R.kernelL2Action hd hΛ t f‖ ≤ 1 * ‖f‖
      rw [one_mul]
      exact R.kernelL2Action_norm_le hd hΛ t f)

private theorem actualAction_zero {d : ℕ} (hd : 2 ≤ d)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) {ω : FieldPair d} {hω : IsRegular Λ ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (R : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1) :
    actualActionCLM hd hΛ R 0 = ContinuousLinearMap.id ℝ _ := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  letI : SigmaFinite (physicalReversibleMeasure ω hd lam) :=
    EinsteinRelation.Diffusion.physicalReversibleMeasure_sigmaFinite hd ω lam
  letI : IsMarkovKernel (R.transitionKernel 0) := R.transitionKernel_isMarkovKernel 0
  have hk := WeightedKernelL2.kernelIntegralL2_coe
    (R.transitionKernel_invariant hd hΛ 0) f
  change R.kernelL2Action hd hΛ 0 f =ᵐ[_] _ at hk
  filter_upwards [hk] with x hx
  change R.kernelL2Action hd hΛ 0 f x = f x
  rw [hx]
  simp only [WeightedKernelL2.kernelIntegral, R.transitionKernel_zero,
    Kernel.id_apply, integral_dirac]

private theorem actual_action_tendsto_zero {d : ℕ} (hd : 2 ≤ d)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) {ω : FieldPair d} {hω : IsRegular Λ ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (R : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    Tendsto (fun t : ℝ≥0 => R.kernelL2Action hd hΛ t f)
      (𝓝[Set.Ioi 0] (0 : ℝ≥0)) (𝓝 f) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  letI : IsLocallyFiniteMeasure (physicalReversibleMeasure ω hd lam) := by
    change IsLocallyFiniteMeasure (densityWeightedMeasure (sourcePhysicalDensity ω hd lam))
    exact densityWeightedMeasure_locallyFinite _ (continuousSourcePhysicalDensity ω hd lam)
  letI : IsFiniteMeasureOnCompacts (physicalReversibleMeasure ω hd lam) :=
    finiteOnCompacts_of_locallyFinite
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  have hdense : Dense {z : Lp ℝ 2 (physicalReversibleMeasure ω hd lam) |
      ∃ g : Vec d → ℝ, (z : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] g ∧
        HasCompactSupport g ∧ ContDiff ℝ (⊤ : ℕ∞) g} :=
    MeasureTheory.Lp.dense_hasCompactSupport_contDiff (by norm_num)
  obtain ⟨U, ⟨g, hUg, hgc, hgd⟩, hu⟩ := hdense.exists_dist_lt f (by positivity : 0 < ε / 3)
  have hu' : dist U f < ε / 3 := by rwa [dist_comm] at hu
  obtain ⟨δ, hδ, ht⟩ := (Metric.tendsto_nhdsWithin_nhds.mp
    (compact_action_tendsto_zero hd hΛ R g hgd hgc U hUg)) (ε / 3) (by positivity)
  refine ⟨δ, hδ, fun t ht0 htδ => ?_⟩
  have hclose : dist (R.kernelL2Action hd hΛ t U) U < ε / 3 := ht ht0 htδ
  have hcontract : dist (R.kernelL2Action hd hΛ t f)
      (R.kernelL2Action hd hΛ t U) ≤ dist f U := by
    rw [dist_eq_norm, dist_eq_norm, ← R.kernelL2Action_sub hd hΛ t f U]
    exact R.kernelL2Action_norm_le hd hΛ t (f - U)
  have htriangle := dist_triangle4 (R.kernelL2Action hd hΛ t f)
    (R.kernelL2Action hd hΛ t U) U f
  rw [dist_comm f U] at hcontract
  linarith

private theorem contractiveSemigroup_continuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : ℝ≥0 → E →L[ℝ] E}
    (hP0 : P 0 = ContinuousLinearMap.id ℝ E)
    (hPm : ∀ s t, P (s + t) = (P s).comp (P t))
    (hPn : ∀ t f, ‖P t f‖ ≤ ‖f‖)
    (hPc : ∀ f, Tendsto (fun t => P t f) (𝓝[>] (0 : ℝ≥0)) (𝓝 f))
    (f : E) : Continuous (fun t => P t f) := by
  have hc0 : Tendsto (fun t => P t f) (𝓝 (0 : ℝ≥0)) (𝓝 f) := by
    have hs : Tendsto (fun t => P t f) (𝓝[{0}] (0 : ℝ≥0)) (𝓝 f) := by
      simpa only [hP0, ContinuousLinearMap.id_apply] using
        (continuousWithinAt_singleton (f := fun t => P t f) (x := 0)).tendsto
    have h := (hPc f).sup hs
    have he : Ici (0 : ℝ≥0) = univ := Set.eq_univ_of_forall (fun t => t.property)
    simpa only [nhdsGT_sup_nhdsWithin_singleton, he, nhdsWithin_univ] using h
  apply continuous_iff_continuousAt.mpr
  intro t
  have hleft : Tendsto (fun s : ℝ≥0 => ‖P (s - t) f - f‖) (𝓝 t) (𝓝 0) := by
    have hz : Tendsto (fun s : ℝ≥0 => s - t) (𝓝 t) (𝓝 0) := by
      have h : Tendsto (fun s : ℝ≥0 => s - t) (𝓝 t) (𝓝 (t - t)) :=
        (show Continuous (fun s : ℝ≥0 => s - t) from
          continuous_id.sub continuous_const).continuousAt
      rwa [tsub_self] at h
    simpa using ((hc0.comp hz).sub (tendsto_const_nhds (x := f))).norm
  have hright : Tendsto (fun s : ℝ≥0 => ‖P (t - s) f - f‖) (𝓝 t) (𝓝 0) := by
    have hz : Tendsto (fun s : ℝ≥0 => t - s) (𝓝 t) (𝓝 0) := by
      have h : Tendsto (fun s : ℝ≥0 => t - s) (𝓝 t) (𝓝 (t - t)) :=
        (show Continuous (fun s : ℝ≥0 => t - s) from
          continuous_const.sub continuous_id).continuousAt
      rwa [tsub_self] at h
    simpa using ((hc0.comp hz).sub (tendsto_const_nhds (x := f))).norm
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun s => dist_nonneg) _ (by simpa using hleft.add hright)
  intro s
  rcases le_total t s with h | h
  · have he : P s f - P t f = P t (P (s - t) f - f) := by
      rw [map_sub, ← ContinuousLinearMap.comp_apply, ← hPm, add_tsub_cancel_of_le h]
    rw [dist_eq_norm, he]
    exact (hPn t _).trans (le_add_of_nonneg_right (norm_nonneg _))
  · have he : P t f - P s f = P s (P (t - s) f - f) := by
      rw [map_sub, ← ContinuousLinearMap.comp_apply, ← hPm, add_tsub_cancel_of_le h]
    rw [dist_comm, dist_eq_norm, he]
    exact (hPn s _).trans (le_add_of_nonneg_left (norm_nonneg _))

private def C0Graph {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : ℝ≥0 → E →L[ℝ] E) (f g : E) : Prop :=
  Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (P t f - f))
    (𝓝[>] (0 : ℝ≥0)) (𝓝 g)

private theorem c0Graph_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {P : ℝ≥0 → E →L[ℝ] E}
    (hP0 : P 0 = ContinuousLinearMap.id ℝ E)
    (hPm : ∀ s t, P (s + t) = (P s).comp (P t))
    (hPc : ∀ f, Continuous (fun t => P t f)) (f : E) (t : ℝ≥0) :
    C0Graph P (∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal f) (P t f - f) := by
  let u : ℝ → E := fun s => P s.toNNReal f
  let F : ℝ → E := fun s => ∫ r in (0 : ℝ)..s, u r
  have hu : Continuous u := (hPc f).comp continuous_real_toNNReal
  have hF (s : ℝ) : HasDerivAt F (u s) s :=
    (hu.integral_hasStrictDerivAt 0 s).hasDerivAt
  have hd : HasDerivAt (fun s : ℝ => F ((t : ℝ) + s) - F s) (P t f - f) 0 := by
    have h := ((hF ((t : ℝ) + 0)).scomp 0
      ((hasDerivAt_id 0).const_add (t : ℝ))).sub (hF 0)
    simp only [u, add_zero, Real.toNNReal_coe, Real.toNNReal_zero, hP0,
      ContinuousLinearMap.id_apply, one_smul] at h
    exact h
  have hslope := (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl (0 : ℝ))).mp
    (hd.hasDerivWithinAt (s := Ioi 0))
  have hcoe : Tendsto (fun h : ℝ≥0 => (h : ℝ)) (𝓝[>] (0 : ℝ≥0)) (𝓝[>] (0 : ℝ)) := by
    simpa only [NNReal.map_coe_nhdsGT, NNReal.coe_zero] using
      (tendsto_map : Tendsto NNReal.toReal (𝓝[>] (0 : ℝ≥0))
        (Filter.map NNReal.toReal (𝓝[>] (0 : ℝ≥0))))
  have hh := hslope.comp hcoe
  apply hh.congr'
  filter_upwards [eventually_mem_nhdsWithin] with h hh
  have hshift : P h (F (t : ℝ)) = F ((t : ℝ) + h) - F (h : ℝ) := by
    change P h (∫ s in (0 : ℝ)..(t : ℝ), u s) = _
    rw [← (P h).intervalIntegral_comp_comm (hu.intervalIntegrable 0 t)]
    have he : (fun s : ℝ => P h (u s)) =ᶠ[ae (volume.restrict (uIoc (0 : ℝ) t))]
        (fun s : ℝ => u (s + h)) := by
      filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
      have hs0 : 0 ≤ s := (min_eq_left t.property ▸ hs.1).le
      dsimp only [u]
      rw [← ContinuousLinearMap.comp_apply, ← hPm, add_comm]
      have ha : s.toNNReal + h = (s + (h : ℝ)).toNNReal := by
        apply NNReal.coe_injective
        simp only [NNReal.coe_add, Real.coe_toNNReal', max_eq_left hs0]
        exact (max_eq_left (add_nonneg hs0 h.property)).symm
      rw [ha]
    rw [intervalIntegral.integral_congr_ae_restrict he,
      intervalIntegral.integral_comp_add_right]
    simp only [zero_add]
    exact eq_sub_of_add_eq' (intervalIntegral.integral_add_adjacent_intervals
      (hu.intervalIntegrable 0 h) (hu.intervalIntegrable h (t + h)))
  simp only [Function.comp_apply, slope_def_module, sub_zero, add_zero, F, intervalIntegral.integral_same]
  rw [← hshift]

private theorem generator_quotient_bounded
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : ℝ≥0 → E →L[ℝ] E}
    (hPn : ∀ t f, ‖P t f‖ ≤ ‖f‖) {f g : E} (hg : C0Graph P f g) :
    ∃ C : ℝ, ∀ t : ℝ≥0, 0 < t → ‖(t : ℝ)⁻¹ • (P t f - f)‖ ≤ C := by
  obtain ⟨δ, hδ, ht⟩ := (Metric.tendsto_nhdsWithin_nhds.mp hg) 1 zero_lt_one
  refine ⟨max (‖g‖ + 1) (δ⁻¹ * (2 * ‖f‖)), fun t ht0 => ?_⟩
  by_cases hsmall : (t : ℝ) < δ
  · have hh := ht ht0 (by
      change |(t : ℝ) - 0| < δ
      simpa only [sub_zero, abs_of_nonneg (show (0 : ℝ) ≤ t from t.property)] using hsmall)
    have hn := norm_le_norm_add_norm_sub g ((t : ℝ)⁻¹ • (P t f - f))
    rw [norm_sub_rev g] at hn
    rw [dist_eq_norm] at hh
    exact (by linarith : ‖(t : ℝ)⁻¹ • (P t f - f)‖ ≤ ‖g‖ + 1).trans (le_max_left _ _)
  · have htpos : 0 < (t : ℝ) := ht0
    have hinv : (t : ℝ)⁻¹ ≤ δ⁻¹ := inv_anti₀ hδ (le_of_not_gt hsmall)
    have hn : ‖P t f - f‖ ≤ 2 * ‖f‖ := by
      exact (norm_sub_le _ _).trans (by linarith [hPn t f])
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr htpos)]
    exact (mul_le_mul hinv hn (norm_nonneg _) (le_of_lt (inv_pos.mpr hδ))).trans
      (le_max_right _ _)

private theorem generator_compact_pairing {d : ℕ} (hd : 2 ≤ d)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) {ω : FieldPair d} {hω : IsRegular Λ ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (R : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (hSmooth : IsSmoothFieldPair ω)
    {v g : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)}
    (hg : C0Graph (actualActionCLM hd hΛ R) v g)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (f0 : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hrep : (f0 : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] f) :
    inner ℝ g f0 = inner ℝ v (compactTestGeneratorL2 hd ω hSmooth lam f hf hc) := by
  obtain ⟨C, hC⟩ := generator_quotient_bounded
    (P := actualActionCLM hd hΛ R) (fun t z => R.kernelL2Action_norm_le hd hΛ t z) hg
  have hbound : ∃ B : ℝ, ∀ t : ℝ≥0, 0 < t →
      semigroupFormDifferenceQuotient ω hd lam R.transitionKernel t v ≤ B := by
    refine ⟨C * ‖v‖, fun t ht => ?_⟩
    rw [semigroupFormDifferenceQuotient_eq_inner hd hΛ R]
    have he : (1 / (t : ℝ)) * inner ℝ (v - R.kernelL2Action hd hΛ t v) v =
        -inner ℝ ((t : ℝ)⁻¹ • (R.kernelL2Action hd hΛ t v - v)) v := by
      rw [real_inner_smul_left, inner_sub_left, inner_sub_left]
      ring
    rw [he]
    exact (neg_le_abs _).trans ((abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hC t ht) (norm_nonneg v)))
  obtain ⟨q, hq⟩ := (R.closedForm_domain v (Lp.memLp v)).mp hbound
  let u := densityWeightedH1GraphEquiv (sourceReducedDensity hd lam)
    (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam) q
  let U : Lp ℝ 2 (physicalReversibleMeasure ω hd lam) :=
    sourcePhysicalValue (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
      (sourcePhysicalDensity ω hd lam) (Real.exp (2 * Λ))
      (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω) u
  have hU : U = v := by
    apply Lp.ext
    have hu := fullDomain_quotient_value_ae hd Λ ω hω lam u
    have hqu : (densityWeightedH1GraphEquiv (sourceReducedDensity hd lam)
        (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)).symm u = q :=
      Equiv.symm_apply_apply _ q
    rw [hqu] at hu
    exact ((sourcePhysicalGraph (sourceReducedDensity hd lam)
      (continuousSourceReducedDensity hd lam) (positiveSourceReducedDensity hd lam)
      (sourcePhysicalDensity ω hd lam) (Real.exp (2 * Λ))
      (sourcePhysicalMeasure_le_reduced ω hd lam Λ hω) u).value_memLp.coeFn_toLp).trans
      (hu.symm.trans hq)
  have hm := compact_mixed_quotient_limit hd hΛ R hSmooth u f hf hc f0 hrep
  change Tendsto (fun t : ℝ≥0 => (1 / (t : ℝ)) *
    inner ℝ (U - R.kernelL2Action hd hΛ t U) f0) _
    (𝓝 (-inner ℝ U (compactTestGeneratorL2 hd ω hSmooth lam f hf hc))) at hm
  rw [hU] at hm
  have hs : Tendsto (fun t : ℝ≥0 => (1 / (t : ℝ)) *
      inner ℝ (v - R.kernelL2Action hd hΛ t v) f0)
      (𝓝[>] (0 : ℝ≥0)) (𝓝 (-inner ℝ g f0)) := by
    have h : Tendsto (fun t : ℝ≥0 =>
        -inner ℝ ((t : ℝ)⁻¹ • (R.kernelL2Action hd hΛ t v - v)) f0)
        (𝓝[>] (0 : ℝ≥0)) (𝓝 (-inner ℝ g f0)) :=
      (hg.inner (tendsto_const_nhds (x := f0))).neg
    apply h.congr'
    exact Eventually.of_forall (fun t => by
      simp only [real_inner_smul_left, inner_sub_left, one_div]
      ring)
  have he := tendsto_nhds_unique hs hm
  exact neg_injective he

theorem gmp_compact_test_strong_generator :
∀ {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 ≤ Λ)
  {ω : FieldPair d} {hω : IsRegular Λ ω} {lam : ℝ}
  {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
  (R : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
    hd Λ hΛ ω hω lam h0 h1) (hSmooth : IsSmoothFieldPair ω)
  (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
  (f0 : Lp ℝ 2 (EinsteinRelation.External.GantertSection7Support.physicalReversibleMeasure ω hd lam)),
  (f0 : Vec d → ℝ) =ᵐ[EinsteinRelation.External.GantertSection7Support.physicalReversibleMeasure ω hd lam] f →
  Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (R.kernelL2Action hd hΛ t f0 - f0))
    (𝓝[Set.Ioi 0] (0 : ℝ≥0))
    (𝓝 (EinsteinFull.C8GMP.compactTestGeneratorL2 hd ω hSmooth lam f hf hc)) := by
  intro d hd Λ hΛ ω hω lam h0 h1 R hSmooth f hf hc f0 hrep
  let P := actualActionCLM hd hΛ R
  let L := compactTestGeneratorL2 hd ω hSmooth lam f hf hc
  have hP0 : P 0 = ContinuousLinearMap.id ℝ _ := actualAction_zero hd hΛ R
  have hPm : ∀ s t, P (s + t) = (P s).comp (P t) := by
    intro s t
    apply ContinuousLinearMap.ext
    intro u
    exact kernelL2Action_add hd hΛ R s t u
  have hPn : ∀ t u, ‖P t u‖ ≤ ‖u‖ := fun t u => R.kernelL2Action_norm_le hd hΛ t u
  have hPc : ∀ u, Continuous (fun t => P t u) :=
    contractiveSemigroup_continuous hP0 hPm hPn (actual_action_tendsto_zero hd hΛ R)
  have hidentity (t : ℝ≥0) : P t f0 - f0 = ∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal L := by
    apply ext_inner_right ℝ
    intro u
    have hpair := generator_compact_pairing hd hΛ R hSmooth
      (c0Graph_integral hP0 hPm hPc u t) f hf hc f0 hrep
    have hu := ((hPc u).comp continuous_real_toNNReal).intervalIntegrable (μ := volume) (0 : ℝ) (t : ℝ)
    have hL := ((hPc L).comp continuous_real_toNNReal).intervalIntegrable (μ := volume) (0 : ℝ) (t : ℝ)
    calc
      inner ℝ (P t f0 - f0) u = inner ℝ (P t u - u) f0 := by
        change inner ℝ (R.kernelL2Action hd hΛ t f0 - f0) u =
          inner ℝ (R.kernelL2Action hd hΛ t u - u) f0
        rw [inner_sub_left, inner_sub_left,
          ← kernelL2Action_symmetric hd hΛ R t f0 u,
          real_inner_comm f0 (R.kernelL2Action hd hΛ t u), real_inner_comm f0 u]
      _ = inner ℝ (∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal u) L := hpair
      _ = inner ℝ L (∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal u) := real_inner_comm _ _
      _ = ∫ s in (0 : ℝ)..(t : ℝ), inner ℝ L (P s.toNNReal u) :=
        ((innerSL ℝ L).intervalIntegral_comp_comm hu).symm
      _ = ∫ s in (0 : ℝ)..(t : ℝ), inner ℝ u (P s.toNNReal L) := by
        apply intervalIntegral.integral_congr
        intro s hs
        change inner ℝ L (R.kernelL2Action hd hΛ s.toNNReal u) =
          inner ℝ u (R.kernelL2Action hd hΛ s.toNNReal L)
        rw [kernelL2Action_symmetric hd hΛ R, real_inner_comm]
      _ = inner ℝ u (∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal L) :=
        (innerSL ℝ u).intervalIntegral_comp_comm hL
      _ = inner ℝ (∫ s in (0 : ℝ)..(t : ℝ), P s.toNNReal L) u := real_inner_comm _ _
  let F : ℝ → Lp ℝ 2 (physicalReversibleMeasure ω hd lam) :=
    fun s => ∫ r in (0 : ℝ)..s, P r.toNNReal L
  have hu : Continuous (fun r : ℝ => P r.toNNReal L) :=
    (hPc L).comp continuous_real_toNNReal
  have hdF : HasDerivAt F L 0 := by
    have h := (hu.integral_hasStrictDerivAt 0 0).hasDerivAt
    simpa only [Real.toNNReal_zero, hP0, ContinuousLinearMap.id_apply] using h
  have hslope := (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl (0 : ℝ))).mp
    (hdF.hasDerivWithinAt (s := Ioi 0))
  have hcoe : Tendsto (fun t : ℝ≥0 => (t : ℝ)) (𝓝[>] (0 : ℝ≥0)) (𝓝[>] (0 : ℝ)) := by
    simpa only [NNReal.map_coe_nhdsGT, NNReal.coe_zero] using
      (tendsto_map : Tendsto NNReal.toReal (𝓝[>] (0 : ℝ≥0))
        (Filter.map NNReal.toReal (𝓝[>] (0 : ℝ≥0))))
  have havg := hslope.comp hcoe
  change Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (P t f0 - f0)) _ (𝓝 L)
  convert havg using 1
  funext t
  simp only [Function.comp_apply, slope_def_module, sub_zero, F,
    intervalIntegral.integral_same, sub_zero]
  rw [hidentity]


-- Exact supervisor contract consumption.
example :
∀ {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 ≤ Λ)
  {ω : FieldPair d} {hω : IsRegular Λ ω} {lam : ℝ}
  {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
  (R : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
    hd Λ hΛ ω hω lam h0 h1) (hSmooth : IsSmoothFieldPair ω)
  (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
  (f0 : Lp ℝ 2 (EinsteinRelation.External.GantertSection7Support.physicalReversibleMeasure ω hd lam)),
  (f0 : Vec d → ℝ) =ᵐ[EinsteinRelation.External.GantertSection7Support.physicalReversibleMeasure ω hd lam] f →
  Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (R.kernelL2Action hd hΛ t f0 - f0))
    (𝓝[Set.Ioi 0] (0 : ℝ≥0))
    (𝓝 (EinsteinFull.C8GMP.compactTestGeneratorL2 hd ω hSmooth lam f hf hc)) := gmp_compact_test_strong_generator

#print axioms gmp_compact_test_strong_generator
#lint
run_cmd do
  let env ← Lean.getEnv
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    if (env.getModuleIdxFor? name).isNone then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
          throwError "Unexpected axiom {ax} in {name}"
      count := count + 1
  Lean.logInfo m!"Standard-axiom audit passed for all {count} local declarations."

end EinsteinFull.Blueprint
