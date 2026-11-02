import EinsteinRelation.Environment.Basic
import EinsteinRelation.Sharpness.CoordinateIterates
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.UniformSpace.CompactConvergence

/-! Borel measurability of the scalar smoothness predicate on the compact-open
space of continuous functions. -/

open MeasureTheory
open Filter Asymptotics
open scoped Topology

namespace EinsteinRelation.Sharpness

instance (d : ℕ) : MeasurableSpace C(Vec d, ℝ) := borel C(Vec d, ℝ)
instance (d : ℕ) : BorelSpace C(Vec d, ℝ) := ⟨rfl⟩

private abbrev SmoothJetIndex (d : ℕ) := List (Fin d)

private abbrev SmoothJet (d : ℕ) := SmoothJetIndex d → C(Vec d, ℝ)

private def smoothJetCompatible {d : ℕ} (J : SmoothJet d) : Prop :=
  ∀ s : List (Fin d), ∀ i : Fin d, ∀ x : Vec d, ∀ t : ℝ,
    J s (x + t • unitVector i) - J s x =
      ∫ u in (0 : ℝ)..t, J (s ++ [i])
        (x + u • unitVector i)

private def smoothJetCompatibleSet {d : ℕ} : Set (SmoothJet d) :=
  {J | smoothJetCompatible J}

private theorem continuousMap_polish {d : ℕ} : PolishSpace C(Vec d, ℝ) := by
  infer_instance

private theorem smoothJetIndex_countable (d : ℕ) : Countable (SmoothJetIndex d) := by
  infer_instance

private theorem smoothJet_polish {d : ℕ} : PolishSpace (SmoothJet d) := by
  letI : Countable (SmoothJetIndex d) := smoothJetIndex_countable d
  haveI : TopologicalSpace.SeparableSpace (SmoothJet d) := by infer_instance
  haveI : TopologicalSpace.IsCompletelyMetrizableSpace (SmoothJet d) := by infer_instance
  infer_instance

private theorem smoothJet_continuous_integral {d : ℕ} (s : List (Fin d)) (i : Fin d)
    (x : Vec d) (t : ℝ) :
    Continuous fun J : SmoothJet d =>
      ∫ u in (0 : ℝ)..t, J (s ++ [i])
        (x + u • unitVector i) := by
  let g : SmoothJet d → ℝ → ℝ := fun J u => J (s ++ [i]) (x + u • unitVector i)
  have hg : Continuous g.uncurry := by
    have hfield : Continuous fun p : SmoothJet d × ℝ =>
        p.1 (s ++ [i]) := (continuous_apply (s ++ [i])).comp continuous_fst
    have harg : Continuous fun p : SmoothJet d × ℝ => x + p.2 • unitVector i :=
      continuous_const.add (continuous_snd.smul continuous_const)
    exact continuous_eval.comp (hfield.prodMk harg)
  simpa [g] using
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := g) hg (0 : ℝ) t)

private theorem smoothJet_isClosed_compatible {d : ℕ} :
    IsClosed (smoothJetCompatibleSet (d := d)) := by
  classical
  simp only [smoothJetCompatibleSet, smoothJetCompatible, Set.setOf_forall]
  refine isClosed_iInter fun (s : List (Fin d)) =>
    isClosed_iInter fun (i : Fin d) =>
    isClosed_iInter fun (x : Vec d) =>
    isClosed_iInter fun (t : ℝ) => ?_
  apply isClosed_eq
  · have h₁ : Continuous fun J : SmoothJet d => J s (x + t • unitVector i) :=
        (continuous_eval_const (x + t • unitVector i)).comp (continuous_apply s)
    have h₂ : Continuous fun J : SmoothJet d => J s x :=
        (continuous_eval_const x).comp (continuous_apply s)
    exact h₁.sub h₂
  · exact smoothJet_continuous_integral s i x t

/-- Compatibility identifies the derivative of each jet component along every coordinate line.
This is the first analytic step in recovering a smooth function from a compatible jet. -/
private theorem smoothJet_hasDerivAt_line {d : ℕ} (J : SmoothJet d)
    (hJ : smoothJetCompatible J) (s : List (Fin d)) (i : Fin d) (x : Vec d) :
    HasDerivAt (fun t : ℝ => J s (x + t • unitVector i)) (J (s ++ [i]) x) 0 := by
  let g : ℝ → ℝ := fun u => J (s ++ [i]) (x + u • unitVector i)
  have hg : Continuous g := by
    dsimp [g]
    exact (J (s ++ [i])).continuous.comp
      (continuous_const.add (continuous_id.smul continuous_const))
  have hFTC : HasDerivAt (fun t : ℝ => ∫ u in (0 : ℝ)..t, g u) (g 0) 0 :=
    intervalIntegral.integral_hasDerivAt_right
      (hg.intervalIntegrable 0 0)
      hg.aestronglyMeasurable.stronglyMeasurableAtFilter
      hg.continuousAt
  have hfun : (fun t : ℝ => J s (x + t • unitVector i)) =
      fun t => (∫ u in (0 : ℝ)..t, g u) + J s x := by
    funext t
    have hcompat := hJ s i x t
    dsimp [g]
    linarith
  rw [hfun]
  simpa [g] using hFTC.add_const (J s x)

/-- Continuous coordinate derivatives assemble into the Fréchet derivative on `Vec d`.
The fixed-interval integrals below make the first-order remainder a finite sum of products
of a coordinate increment and a continuous error term. -/
private theorem smoothJet_hasFDerivAt {d : ℕ} (J : SmoothJet d)
    (hJ : smoothJetCompatible J) (s : List (Fin d)) (x : Vec d) :
    ∃ L : Vec d →L[ℝ] ℝ, HasFDerivAt (J s) L x ∧
      ∀ i : Fin d, L (unitVector i) = J (s ++ [i]) x := by
  classical
  let jetPrefix : Vec d → ℕ → Vec d := fun z k j => x j + if j.val < k then z j else 0
  let phi : Fin d → Vec d → ℝ := fun i z =>
    ∫ u in (0 : ℝ)..1, J (s ++ [i])
      (jetPrefix z i.val + (u * z i) • unitVector i)
  let L : Vec d →L[ℝ] ℝ :=
    ∑ i : Fin d, (ContinuousLinearMap.proj i).smulRight (phi i 0)
  have hprefix_zero (z : Vec d) : jetPrefix z 0 = x := by
    ext j
    simp [jetPrefix]
  have hprefix_end (z : Vec d) : jetPrefix z d = x + z := by
    ext j
    simp [jetPrefix, j.isLt]
  have hprefix_succ (z : Vec d) (k : ℕ) (hk : k < d) :
      jetPrefix z (k + 1) = jetPrefix z k + z ⟨k, hk⟩ • unitVector ⟨k, hk⟩ := by
    ext j
    change x j + (if j.val < k + 1 then z j else 0) =
      x j + (if j.val < k then z j else 0) +
        z ⟨k, hk⟩ * unitVector ⟨k, hk⟩ j
    simp only [unitVector, Pi.single_apply]
    by_cases hj : j.val < k
    · have hj' : j.val < k + 1 := by omega
      have hneq : j ≠ ⟨k, hk⟩ := by
        intro he
        have hval := congrArg Fin.val he
        have hval' : j.val = k := by simpa using hval
        omega
      simp [hj, hj', hneq]
    · by_cases hEq : j.val = k
      · have hj' : j.val < k + 1 := by omega
        have hj_eq : j = ⟨k, hk⟩ := Fin.ext hEq
        subst j
        simp [hj']
      · have hj' : ¬ j.val < k + 1 := by omega
        have hneq : j ≠ ⟨k, hk⟩ := by
          intro he
          have hval := congrArg Fin.val he
          exact hEq hval
        simp [hj, hj', hneq]
  have hphi_cont : ∀ i : Fin d, Continuous (phi i) := by
    intro i
    let g : Vec d → ℝ → ℝ := fun z u =>
      J (s ++ [i]) (jetPrefix z i.val + (u * z i) • unitVector i)
    have hprefix_cont : Continuous fun p : Vec d × ℝ => jetPrefix p.1 i.val := by
      apply continuous_pi
      intro j
      by_cases hj : j.val < i.val
      · refine (show Continuous fun p : Vec d × ℝ => x j + p.1 j by fun_prop).congr fun p => ?_
        simp [jetPrefix, hj]
      · simpa [jetPrefix, hj] using
          (continuous_const : Continuous fun _ : Vec d × ℝ => x j)
    have harg : Continuous fun p : Vec d × ℝ =>
        jetPrefix p.1 i.val + (p.2 * p.1 i) • unitVector i := by
      exact hprefix_cont.add
        ((continuous_snd.mul ((continuous_apply i).comp continuous_fst)).smul continuous_const)
    have hg : Continuous g.uncurry := by
      dsimp [g]
      exact (J (s ++ [i])).continuous.comp harg
    simpa [phi, g] using
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (f := g) hg (0 : ℝ) 1)
  have hphi_zero (i : Fin d) : phi i 0 = J (s ++ [i]) x := by
    simp [phi, jetPrefix]
  have hL_apply (z : Vec d) : L z = ∑ i : Fin d, z i * phi i 0 := by
    simp [L, ContinuousLinearMap.smulRight_apply]
  have htotal (z : Vec d) :
      J s (x + z) - J s x = ∑ i : Fin d, z i * phi i z := by
    have htel :
        (∑ k ∈ Finset.range d,
          (J s (jetPrefix z (k + 1)) - J s (jetPrefix z k))) =
          J s (x + z) - J s x := by
        rw [Finset.sum_range_sub (fun k => J s (jetPrefix z k)), hprefix_end, hprefix_zero]
    rw [← htel]
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    have hstep := hprefix_succ z i.val i.isLt
    have hcompat := hJ s i (jetPrefix z i.val) (z i)
    have hchange :
        (∫ u in (0 : ℝ)..z i, J (s ++ [i]) (jetPrefix z i.val + u • unitVector i)) =
          z i * phi i z := by
      simpa [phi, mul_comm, smul_eq_mul] using
        (intervalIntegral.smul_integral_comp_mul_left (z i)
          (f := fun u : ℝ =>
            J (s ++ [i]) (jetPrefix z i.val + u • unitVector i))
          (a := (0 : ℝ)) (b := 1)).symm
    rw [hstep]
    calc
      (J s) (jetPrefix z i.val + z i • unitVector i) - (J s) (jetPrefix z i.val) =
          ∫ u in (0 : ℝ)..z i, J (s ++ [i]) (jetPrefix z i.val + u • unitVector i) := hcompat
      _ = z i * phi i z := hchange
  have hcoord : ∀ i : Fin d,
      (fun z : Vec d => z i) =O[𝓝 (0 : Vec d)] (fun z => ‖z‖) := by
    intro i
    refine isBigO_iff.2 ⟨1, ?_⟩
    filter_upwards [] with z
    simpa using (norm_le_pi_norm z i)
  have hdelta : ∀ i : Fin d,
      (fun z : Vec d => phi i z - phi i 0) =o[𝓝 (0 : Vec d)] (fun _ => (1 : ℝ)) := by
    intro i
    rw [isLittleO_one_iff]
    have h2 : Tendsto (fun z : Vec d => phi i z - phi i 0) (𝓝 0) (𝓝 (phi i 0 - phi i 0)) :=
      ((hphi_cont i).tendsto 0).sub tendsto_const_nhds
    rwa [sub_self] at h2
  have hterm : ∀ i : Fin d,
      (fun z : Vec d => z i * (phi i z - phi i 0)) =o[𝓝 (0 : Vec d)] (fun z => ‖z‖) := by
    intro i
    simpa [mul_one] using (hcoord i).mul_isLittleO (hdelta i)
  have hrem :
      (fun z : Vec d => J s (x + z) - J s x - L z) =o[𝓝 (0 : Vec d)] (fun z => ‖z‖) := by
    have hsum :
        (fun z : Vec d => ∑ i : Fin d, z i * (phi i z - phi i 0)) =o[𝓝 (0 : Vec d)]
          (fun z => ‖z‖) := by
      exact (Asymptotics.IsLittleO.sum (s := Finset.univ) (A := fun i z =>
        z i * (phi i z - phi i 0)) (fun i hi => hterm i)).congr_left
        fun z => Finset.sum_apply z _ _
    apply hsum.congr_left
    intro z
    rw [htotal z, hL_apply]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
  refine ⟨L, ?_, ?_⟩
  · rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    rw [isLittleO_iff]
    intro c hc
    have h := (isLittleO_iff.1 hrem) hc
    filter_upwards [h] with z hz
    simpa using hz
  · intro i
    rw [hL_apply]
    simp [hphi_zero, unitVector, Pi.single_apply]

private theorem smoothJet_fderiv_apply {d : ℕ} (J : SmoothJet d)
    (hJ : smoothJetCompatible J) (s : List (Fin d)) (x v : Vec d) :
    (fderiv ℝ (J s) x) v = ∑ i : Fin d, v i * J (s ++ [i]) x := by
  obtain ⟨L, hL, hcoord⟩ := smoothJet_hasFDerivAt J hJ s x
  have hv : v = ∑ i : Fin d, v i • unitVector i := by
    ext j
    simp [unitVector, Pi.single_apply]
  rw [hL.fderiv, hv]
  simp only [map_sum, map_smul]
  change (∑ i : Fin d, v i * L (unitVector i)) = _
  apply Finset.sum_congr rfl
  intro i hi
  rw [hcoord i]
  simp [unitVector, Pi.single_apply]

private theorem smoothJet_contDiff {d : ℕ} (J : SmoothJet d)
    (hJ : smoothJetCompatible J) :
    ∀ n : ℕ, ∀ s : List (Fin d), ContDiff ℝ n (J s) := by
  intro n
  induction n with
  | zero =>
      intro s
      exact contDiff_zero.2 (J s).continuous
  | succ n ih =>
      intro s
      change ContDiff ℝ ((n : ℕ∞) + 1) (J s)
      rw [contDiff_succ_iff_fderiv_apply]
      refine ⟨?_, ?_, ?_⟩
      · intro x
        exact (smoothJet_hasFDerivAt J hJ s x).choose_spec.1.differentiableAt
      · intro hn
        simp at hn
      · intro v
        have hformula : (fun x => fderiv ℝ (J s) x v) =
            fun x => ∑ i : Fin d, v i * J (s ++ [i]) x := by
          funext x
          exact smoothJet_fderiv_apply J hJ s x v
        rw [hformula]
        apply ContDiff.sum
        intro i hi
        exact (contDiff_const : ContDiff ℝ n (fun _ : Vec d => v i)).mul
          (ih (s ++ [i]))

private theorem smoothJet_contDiff_infty {d : ℕ} (J : SmoothJet d)
    (hJ : smoothJetCompatible J) (s : List (Fin d)) :
    ContDiff ℝ (⊤ : ℕ∞) (J s) := by
  rw [contDiff_infty]
  intro n
  exact smoothJet_contDiff J hJ n s

/-- A compatible jet is determined by its root component. -/
theorem smoothJet_eq_of_root_eq {d : ℕ} (J K : SmoothJet d)
    (hJ : smoothJetCompatible J) (hK : smoothJetCompatible K) (hroot : J [] = K []) :
    J = K := by
  funext s
  have hrev : ∀ l : List (Fin d), J l.reverse = K l.reverse := by
    intro l
    induction l with
    | nil => simpa using hroot
    | cons i l ih =>
        rw [List.reverse_cons]
        ext x
        have hfun : (J l.reverse : Vec d → ℝ) = K l.reverse := congrArg DFunLike.coe ih
        have hfd : fderiv ℝ (J l.reverse) x = fderiv ℝ (K l.reverse) x := by
          rw [hfun]
        have hJderiv := smoothJet_fderiv_apply J hJ l.reverse x (unitVector i)
        have hKderiv := smoothJet_fderiv_apply K hK l.reverse x (unitVector i)
        have hJcoord : (fderiv ℝ (J l.reverse) x) (unitVector i) = J (l.reverse ++ [i]) x := by
          simpa [unitVector, Pi.single_apply] using hJderiv
        have hKcoord : (fderiv ℝ (K l.reverse) x) (unitVector i) = K (l.reverse ++ [i]) x := by
          simpa [unitVector, Pi.single_apply] using hKderiv
        rw [← hJcoord, hfd, hKcoord]
  have hs := hrev s.reverse
  simpa using hs

private noncomputable def smoothJetOfSmoothFunction {d : ℕ} (f : C(Vec d, ℝ))
    (hf : ContDiff ℝ (⊤ : ℕ∞) (fun x => f x)) : SmoothJet d := fun s =>
  ⟨iteratedCoordinateDerivative s.reverse f,
    (contDiff_iteratedCoordinateDerivative f hf s.reverse).continuous⟩

private theorem smoothJetOfSmoothFunction_root {d : ℕ} (f : C(Vec d, ℝ))
    (hf : ContDiff ℝ (⊤ : ℕ∞) (fun x => f x)) :
    smoothJetOfSmoothFunction f hf [] = f := by
  ext x
  simp [smoothJetOfSmoothFunction]

private theorem coordinateLine_integral {d : ℕ} (g : Vec d → ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (i : Fin d) (x : Vec d) (t : ℝ) :
    g (x + t • unitVector i) - g x =
      ∫ u in (0 : ℝ)..t, coordinateDerivative i g (x + u • unitVector i) := by
  let q : ℝ → ℝ := fun u => g (x + u • unitVector i)
  have hline : ∀ u : ℝ, HasDerivAt q (coordinateDerivative i g (x + u • unitVector i)) u := by
    intro u
    have harg : HasFDerivAt (fun v : ℝ => x + v • unitVector i)
        ((1 : ℝ →L[ℝ] ℝ).smulRight (unitVector i) : ℝ →L[ℝ] Vec d) u := by
      have hsmul : HasFDerivAt (fun v : ℝ => v • unitVector i)
          ((1 : ℝ →L[ℝ] ℝ).smulRight (unitVector i) : ℝ →L[ℝ] Vec d) u :=
        (hasFDerivAt_id u).smul_const (unitVector i)
      simpa using hsmul.const_add x
    have hg1 : ContDiff ℝ (1 : ℕ∞) g := by
      have hall := hg
      rw [contDiff_infty] at hall
      exact hall 1
    have hgd : DifferentiableAt ℝ g (x + u • unitVector i) :=
      hg1.differentiable_one.differentiableAt
    have hcomp := hgd.hasFDerivAt.comp u harg
    have hnext : coordinateDerivative i g (x + u • unitVector i) =
        (fderiv ℝ g (x + u • unitVector i)) (unitVector i) := rfl
    have hd : ((fderiv ℝ g (x + u • unitVector i)).comp
        ((1 : ℝ →L[ℝ] ℝ).smulRight (unitVector i))) 1 =
        coordinateDerivative i g (x + u • unitVector i) := by
      rw [hnext]
      simp
    rw [← hd]
    exact hcomp.hasDerivAt
  have hnextcont : Continuous fun u : ℝ => coordinateDerivative i g (x + u • unitVector i) := by
    have hcoord : ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative i g) := by
      unfold coordinateDerivative
      exact (hg.fderiv_right (le_of_eq ENat.coe_top_add_one)).clm_apply contDiff_const
    exact hcoord.continuous.comp
        (continuous_const.add (continuous_id.smul continuous_const))
  have hint : IntervalIntegrable
      (fun u : ℝ => coordinateDerivative i g (x + u • unitVector i)) volume 0 t :=
    hnextcont.intervalIntegrable 0 t
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u _hu => hline u) hint
  simpa [q] using hFTC.symm

/-- Every smooth scalar function has its actual iterated coordinate derivatives as a compatible
jet. -/
theorem exists_compatible_smoothJet {d : ℕ} (f : C(Vec d, ℝ))
    (hf : ContDiff ℝ (⊤ : ℕ∞) (fun x => f x)) :
    ∃ J : SmoothJet d, smoothJetCompatible J ∧ J [] = f := by
  let J := smoothJetOfSmoothFunction f hf
  refine ⟨J, ?_, smoothJetOfSmoothFunction_root f hf⟩
  intro s i x t
  change iteratedCoordinateDerivative s.reverse f (x + t • unitVector i) -
    iteratedCoordinateDerivative s.reverse f x =
      ∫ u in (0 : ℝ)..t, iteratedCoordinateDerivative (s ++ [i]).reverse f
        (x + u • unitVector i)
  have hnext : iteratedCoordinateDerivative (s ++ [i]).reverse f =
      coordinateDerivative i (iteratedCoordinateDerivative s.reverse f) := by
    simp [List.reverse_append]
  rw [hnext]
  exact coordinateLine_integral (iteratedCoordinateDerivative s.reverse f)
    (contDiff_iteratedCoordinateDerivative f hf s.reverse) i x t

private def smoothFunctionSet {d : ℕ} : Set C(Vec d, ℝ) :=
  {f | ContDiff ℝ (⊤ : ℕ∞) (fun x => f x)}

private def smoothJetRootProjection {d : ℕ} : SmoothJet d → C(Vec d, ℝ) := fun J => J []

private theorem smoothJetRootProjection_continuous {d : ℕ} :
    Continuous (smoothJetRootProjection (d := d)) :=
  continuous_apply []

private theorem smoothJetRootProjection_injectiveOn_compatible {d : ℕ} :
    Set.InjOn (smoothJetRootProjection (d := d)) (smoothJetCompatibleSet (d := d)) := by
  intro J hJ K hK hroot
  change smoothJetCompatible J at hJ
  change smoothJetCompatible K at hK
  exact smoothJet_eq_of_root_eq J K hJ hK hroot

private theorem smoothFunctionSet_eq_smoothJetRootProjection_image {d : ℕ} :
    smoothFunctionSet (d := d) =
      smoothJetRootProjection (d := d) '' smoothJetCompatibleSet (d := d) := by
  ext f
  constructor
  · intro hf
    obtain ⟨J, hJ, hroot⟩ := exists_compatible_smoothJet f hf
    exact ⟨J, hJ, hroot⟩
  · rintro ⟨J, hJ, rfl⟩
    exact smoothJet_contDiff_infty J hJ []

theorem measurableSet_contDiff_continuousMap {d : ℕ} :
    MeasurableSet {f : C(Vec d, ℝ) | ContDiff ℝ (⊤ : ℕ∞) (fun x => f x)} := by
  letI : Countable (SmoothJetIndex d) := smoothJetIndex_countable d
  letI : PolishSpace (SmoothJet d) := smoothJet_polish
  letI : MeasurableSpace (SmoothJet d) := borel (SmoothJet d)
  letI : BorelSpace (SmoothJet d) := ⟨rfl⟩
  rw [show {f : C(Vec d, ℝ) | ContDiff ℝ (⊤ : ℕ∞) (fun x => f x)} =
      smoothJetRootProjection (d := d) '' smoothJetCompatibleSet (d := d) from
    smoothFunctionSet_eq_smoothJetRootProjection_image]
  exact MeasurableSet.image_of_continuousOn_injOn
    (smoothJet_isClosed_compatible.measurableSet)
    (smoothJetRootProjection_continuous.continuousOn.mono (Set.subset_univ _))
    smoothJetRootProjection_injectiveOn_compatible

end EinsteinRelation.Sharpness
