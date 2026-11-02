import EinsteinFull.Frozen.ReducedLaw
import EinsteinFull.Frozen.StructuralData
import EinsteinFull.Calculus.C10LocalTimeStationaryAverage
import EinsteinFull.Calculus.C1EndpointFiniteP
import EinsteinFull.Calculus.K5FixedAnnularReconstruction
import EinsteinFull.Work.W4.ActualLateForceHomogeneousPropagationProof
import EinsteinFull.Calculus.RadialTransposeCutoffLimitSupport
import EinsteinFull.Calculus.LocalEnergySupport
import EinsteinFull.Calculus.S4ReducedCoefficientSupport
import EinsteinFull.Calculus.S1CovarianceL2Support
import EinsteinFull.Blueprint.G2.Proofs.S1FluxIdentity
import EinsteinFull.Blueprint.Foundation.node_e_u3A_local_u2D_time
import EinsteinRelation.Correctors.FrobeniusDilation
import EinsteinFull.Work.W3.GaussianDerivativeAveragingSupport
import EinsteinRelation.TimeChange.EuclideanTransport
import PDEFoundation.Measure.BallVolume
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MeasureTheory
open scoped BigOperators NNReal ENNReal

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull

/-- Antisymmetrizing a matrix center contracts its squared distance to a skew field. -/
theorem carverS_flux_block_skew_center {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀)
    (S0 : Fin d → FieldPair d → Vec d → Mat d)
    (hskew : ∀ᵐ ω ∂reducedLaw Q, ∀ i : Fin d, ∀ x : Vec d,
      (S0 i ω x).transpose = -(S0 i ω x)) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ (i : Fin d) (b : Mat d),
      let c : Mat d := fun j k => (b j k - b k j) / 2
      (∀ j k : Fin d, c j k = -c k j) ∧ ∀ x : Vec d,
        (∑ j : Fin d, ∑ k : Fin d, (S0 i ω x j k - c j k) ^ 2) ≤
          ∑ j : Fin d, ∑ k : Fin d, (S0 i ω x j k - b j k) ^ 2 := by
  filter_upwards [hskew] with ω hω
  intro i b
  dsimp only
  constructor
  · intro j k
    ring
  · intro x
    have hentry (j k : Fin d) : S0 i ω x k j = -S0 i ω x j k :=
      congrFun (congrFun (hω i x) j) k
    have hpair (j k : Fin d) :
        2 * (S0 i ω x j k - (b j k - b k j) / 2) ^ 2 ≤
          (S0 i ω x j k - b j k) ^ 2 +
            (S0 i ω x k j - b k j) ^ 2 := by
      rw [hentry j k]
      nlinarith [sq_nonneg (b j k + b k j)]
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      Finset.sum_le_sum (s := Finset.univ) (fun k _ => hpair j k))
    have hswap :
        (∑ j : Fin d, ∑ k : Fin d, (S0 i ω x k j - b k j) ^ 2) =
          ∑ j : Fin d, ∑ k : Fin d, (S0 i ω x j k - b j k) ^ 2 :=
      Finset.sum_comm
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
    rw [hswap] at hsum
    linarith

/-- Stationarity controls the terminal local value by the actual transpose Lp growth. -/
theorem carverS_transpose_terminal_local_value_moment (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) (p : ℝ) (hp : 2 ≤ p) :
    ∃ C Cp : ℝ, 1 ≤ C ∧ 0 < Cp ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (i : Fin d) (ζ : ℂ)
      (P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q i ζ P → IsComplexTransposeSemigroup Q P T →
    ∀ f : Lp ℂ 2 (reducedLaw Q), MemLp f (ENNReal.ofReal p) (reducedLaw Q) →
    ∀ (t : ℝ≥0), 0 < (t : ℝ) → ∀ (ρ : ℝ) (z : Vec d),
      Real.sqrt (t : ℝ) ≤ ρ →
      let A := fun ω : FieldPair d => Real.sqrt
        (⨍ x in {x : Vec d | euclideanNorm (x - z) ≤ ρ}, ‖T t f (translate x ω)‖ ^ 2)
      MemLp A (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm A (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
          C * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) *
            Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
              (eLpNorm f (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  let a : ℝ := p / 2 - 1
  have ha : 0 ≤ a := by dsimp [a]; linarith only [hp]
  have hpa : 2 * (1 + a) = p := by dsimp [a]; ring
  let K := Real.exp (2 * D.ellipticity) * D.ellipticity
  let c := (d : ℝ) * K * (K * (1 + 2 * a)) ^ 2
  have hK : 0 ≤ K := mul_nonneg (Real.exp_pos _).le
    (zero_le_one.trans D.one_le_ellipticity)
  have hd0 : 0 ≤ (d : ℝ) :=
    (by norm_num : (0 : ℝ) ≤ 2).trans (by exact_mod_cast hd)
  have hc : 0 ≤ c := mul_nonneg (mul_nonneg hd0 hK) (sq_nonneg _)
  refine ⟨1, c + 1, le_rfl, by positivity, ?_⟩
  intro Q i ζ P T hP hT f hf t ht ρ z hρ
  have hf' : MemLp f (ENNReal.ofReal (2 * (1 + a))) (reducedLaw Q) := by
    rwa [hpa]
  have hout := (hT.power_moment_growth hP ha f hf' t).1
  rw [hpa] at hout
  have hgrowth := hT.eLpNorm_growth hP ha f hf' t
  rw [hpa] at hgrowth
  have hrate : ((d : ℝ) * K * (‖ζ‖ * K * (1 + 2 * a)) ^ 2) * (t : ℝ) =
      c * ‖ζ‖ ^ 2 * (t : ℝ) := by dsimp [c]; ring
  change eLpNorm (T t f) (ENNReal.ofReal p) (reducedLaw Q) ≤
    eLpNorm f (ENNReal.ofReal p) (reducedLaw Q) *
      ENNReal.ofReal (Real.exp (((d : ℝ) * K *
        (‖ζ‖ * K * (1 + 2 * a)) ^ 2) * (t : ℝ))) at hgrowth
  rw [hrate] at hgrowth
  have hgrowthReal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top hf.ne_top ENNReal.ofReal_ne_top) hgrowth
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at hgrowthReal
  let B := {x : Vec d | euclideanNorm (x - z) ≤ ρ}
  have hr : 0 < ρ := (Real.sqrt_pos.mpr ht).trans_le hρ
  have hball : B = PDE.euclideanClosedBall z ρ := by
    ext x
    change Real.sqrt (euclideanSq (x - z)) ≤ ρ ↔ PDE.vecNormSq (x - z) ≤ ρ ^ 2
    rw [Real.sqrt_le_iff]
    exact and_iff_right hr.le
  have hv0 : volume B ≠ 0 := ne_of_gt
    ((PDE.volume_euclideanBall_pos z hr).trans_le
      (measure_mono (by rw [hball]; exact PDE.euclideanBall_subset_euclideanClosedBall z ρ)))
  have hvfin : volume B ≠ ∞ := (isCompact_physical_euclidean_closedBall z ρ).measure_ne_top
  let κ : Measure (Vec d) := (volume B)⁻¹ • volume.restrict B
  let : IsProbabilityMeasure κ := ⟨by
    dsimp [κ]
    rw [Measure.restrict_apply_univ]
    exact ENNReal.inv_mul_cancel hv0 hvfin⟩
  let M := (eLpNorm (T t f) (ENNReal.ofReal p) (reducedLaw Q)).toReal
  obtain ⟨hA, hAnorm⟩ := local_time_stationary_square_average_memLp Q
    (Measure.dirac (0 : ℝ)) κ p M hp ENNReal.toReal_nonneg
    (fun q => T t f q.2) ((Lp.stronglyMeasurable (T t f)).measurable.comp measurable_snd)
    (Filter.Eventually.of_forall fun _ => ⟨hout, le_rfl⟩)
  have havg (ω : FieldPair d) :
      (∫ s : ℝ, ∫ y, ‖T t f (translate y ω)‖ ^ 2 ∂κ ∂Measure.dirac 0) =
        ⨍ y in B, ‖T t f (translate y ω)‖ ^ 2 := by
    rw [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
    simp only [average_eq', Measure.restrict_apply_univ]
    rfl
  simp only [havg] at hA hAnorm
  refine ⟨hA, hAnorm.trans (hgrowthReal.trans ?_)⟩
  have he : Real.exp (c * ‖ζ‖ ^ 2 * (t : ℝ)) ≤
      Real.exp ((c + 1) * ‖ζ‖ ^ 2 * (t : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_nonneg (sq_nonneg ‖ζ‖) t.coe_nonneg]
  have hfac : 1 ≤ 1 + ‖ζ‖ * Real.sqrt (t : ℝ) :=
    le_add_of_nonneg_right (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
  calc
    _ ≤ (eLpNorm f (ENNReal.ofReal p) (reducedLaw Q)).toReal *
        Real.exp ((c + 1) * ‖ζ‖ ^ 2 * (t : ℝ)) :=
      mul_le_mul_of_nonneg_left he ENNReal.toReal_nonneg
    _ ≤ 1 * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) *
        Real.exp ((c + 1) * ‖ζ‖ ^ 2 * (t : ℝ)) *
          (eLpNorm f (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
      have hn : 0 ≤ (eLpNorm f (ENNReal.ofReal p) (reducedLaw Q)).toReal :=
        ENNReal.toReal_nonneg
      have hm := mul_le_mul_of_nonneg_right hfac (mul_nonneg hn
        (Real.exp_pos ((c + 1) * ‖ζ‖ ^ 2 * (t : ℝ))).le)
      convert hm using 1 <;> ring

/-- Skew projection also contracts the normalized spatial oscillation of the actual field. -/
theorem carverS_flux_block_skew_local_oscillation {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀)
    (S : Fin d → FieldPair d → Vec d → Mat d)
    (hcont : ∀ᵐ ω ∂reducedLaw Q, ∀ i j k : Fin d,
      Continuous (fun x => S i ω x j k))
    (hskew : ∀ᵐ ω ∂reducedLaw Q, ∀ i : Fin d, ∀ x : Vec d,
      (S i ω x).transpose = -(S i ω x)) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ (i : Fin d) (b : Mat d) (z : Vec d) (ρ : ℝ),
      let B := {x : Vec d | euclideanNorm (x - z) < ρ}
      let c : Mat d := fun j k => (b j k - b k j) / 2
      (∀ j k : Fin d, c j k = -c k j) ∧
      Real.sqrt ((volume B).toReal⁻¹ * ∫ x in B, frobeniusNorm (S i ω x - c) ^ 2) ≤
        Real.sqrt ((volume B).toReal⁻¹ * ∫ x in B, frobeniusNorm (S i ω x - b) ^ 2) := by
  filter_upwards [hcont, carverS_flux_block_skew_center Q S hskew] with ω hω hproj
  intro i b z ρ B c
  refine ⟨(hproj i b).1, Real.sqrt_le_sqrt ?_⟩
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ENNReal.toReal_nonneg)
  have hint (b' : Mat d) :
      IntegrableOn (fun x => frobeniusNorm (S i ω x - b') ^ 2) B := by
    have hc : Continuous (fun x => frobeniusNorm (S i ω x - b') ^ 2) := by
      simp_rw [Correctors.frobeniusNorm_sq_eq_sum]
      exact continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ =>
        ((hω i j k).sub continuous_const).pow 2
    exact (hc.continuousOn.integrableOn_compact
      (isCompact_physical_euclidean_closedBall z ρ)).mono_set
        (fun x hx => show euclideanNorm (x - z) ≤ ρ from
          le_of_lt (show euclideanNorm (x - z) < ρ from hx))
  apply setIntegral_mono_ae (hint c) (hint b)
  exact Filter.Eventually.of_forall fun x => by
    simp only [Correctors.frobeniusNorm_sq_eq_sum, Matrix.sub_apply]
    exact (hproj i b).2 x

/-- The source-selected pair has admissible skew centers on the same good events and
supplies the actual endpoint identity. The constants precede the environment law. -/
theorem carverS_flux_block_selected_pair (hsp : node_e_u3A_sublinear_u2D_pairStmt)
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ κ C c : ℝ, 0 < κ ∧ κ < 1 / 2 ∧ 1 ≤ C ∧ 0 < c ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
      HasSmoothBounds D Q →
      ∃ (φ : Fin d → FieldPair d → Vec d → ℝ)
        (S : Fin d → FieldPair d → Vec d → Mat d),
        (∀ᵐ ω ∂reducedLaw Q, ∀ i : Fin d,
          ContDiff ℝ (⊤ : ℕ∞) (φ i ω) ∧
          (∀ j k : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => S i ω x j k)) ∧
          (∀ x, (S i ω x).transpose = -(S i ω x)) ∧
          ∀ᵐ x ∂(volume : Measure (Vec d)),
            (∀ j : Fin d, fderiv ℝ (φ i ω) x (unitVector j) =
              correctorGradient Q i (translate x ω) j) ∧
            ∀ j : Fin d,
              (∑ k : Fin d, fderiv ℝ (fun y => S i ω y k j) x (unitVector k)) =
                ((ω.1 x).mulVec (unitVector i +
                  WithLp.ofLp (correctorGradient Q i (translate x ω)))) j -
                    homogenizedCoefficient Q j i) ∧
        (∀ (r : ℝ), 1 ≤ r → ∀ z : Vec d,
          ∃ E : Set (FieldPair d), MeasurableSet E ∧
            reducedLaw Q Eᶜ ≤ ENNReal.ofReal
              (C * Real.exp (-c * r ^ ((d : ℝ) / 2))) ∧
            ∀ ω ∈ E, ∃ (a : Fin d → ℝ) (b : Fin d → Mat d),
              (∀ i j k : Fin d, b i j k = -b i k j) ∧
              let B := {x : Vec d | euclideanNorm (x - z) < C * r}
              (∑ i : Fin d, (
                Real.sqrt ((volume B).toReal⁻¹ *
                  ∫ x in B, |φ i ω x - a i| ^ 2) +
                Real.sqrt ((volume B).toReal⁻¹ *
                  ∫ x in B, frobeniusNorm (S i ω x - b i) ^ 2))) ≤
                    C * r ^ (1 - κ)) ∧
        ∀ (hQ : HasSmoothBounds D Q)
          (β : Fin d → Lp ℂ 2 (reducedLaw Q))
          (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
          (μ : Lp ℂ 2 (reducedLaw Q)),
          IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
          IsReducedClockObservation Q μ → ∀ ζ : ℂ,
        ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
          IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
          IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
          let U := fun t => indexedEndpoint hd Q ν ζ P Pdag β a μ t
          ∃ G J : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
            (∀ t : ℝ≥0, 0 < (t : ℝ) →
              IsEndpointWeakFlux hd Q ν ζ a (U t) (G t) (J t)) ∧
            ∀ t : ℝ≥0, 0 < (t : ℝ) →
              DifferentiableAt ℝ (fun r : ℝ => U r.toNNReal) (t : ℝ) ∧
              ∀ᵐ ω ∂reducedLaw Q, ∀ i : Fin d,
              ∀ (cφ : ℝ) (cS : Fin d → Fin d → ℝ),
                (∀ k j, cS k j = -cS j k) →
              ∀ ψ : Vec d → ℂ,
                ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
                let u := fun x : Vec d => U t (translate x ω)
                let g := fun (x : Vec d) (j : Fin d) => G t j (translate x ω)
                let ut := fun x : Vec d =>
                  deriv (fun r : ℝ => U r.toNNReal) (t : ℝ) (translate x ω)
                let c := ζ * ∫ ω, ∑ k : Fin d,
                  a k ⟨0, by omega⟩ ω * G t k ω ∂reducedLaw Q
                let F := fun (x : Vec d) (j : Fin d) => g x j -
                  match ν with
                  | .inr true =>
                    2 * ζ * (unitVector (⟨0, by omega⟩ : Fin d) j : ℂ) * u x
                  | _ => 0
                let divAF := fun x : Vec d => 2 * ut x +
                  match ν with
                  | .inr true => 0
                  | _ => 2 * c - 2 * ζ * (∑ k : Fin d,
                      (ω.1 x k ⟨0, by omega⟩ : ℂ) * g x k)
                (∫ x, J t i (translate x ω) * ψ x) =
                  (∫ x, ((φ i ω x - cφ : ℝ) : ℂ) * divAF x * ψ x) +
                  (∫ x, ((φ i ω x - cφ : ℝ) : ℂ) *
                    (∑ k : Fin d, (∑ j : Fin d, (ω.1 x k j : ℂ) * F x j) *
                      fderiv ℝ ψ x (unitVector k))) -
                  (∫ x, ∑ k : Fin d, ∑ j : Fin d,
                    ((S i ω x k j - cS k j : ℝ) : ℂ) * F x j *
                      fderiv ℝ ψ x (unitVector k)) +
                  match ν with
                  | .inr true => 2 * ζ * (∫ x, (∑ k : Fin d,
                      ((S i ω x k ⟨0, by omega⟩ - cS k ⟨0, by omega⟩ : ℝ) : ℂ) *
                        g x k) * ψ x)
                  | _ => 0 := by
  classical
  obtain ⟨κ, C, c, hκ, hκhalf, hC, hc, hpairs⟩ := hsp d hd D
  refine ⟨κ, C, c, hκ, hκhalf, hC, hc, ?_⟩
  intro Q hQ
  obtain ⟨φ, S, hgood, hosc⟩ := hpairs Q hQ
  have hcont := hgood.mono fun ω h i j k => ((h i).2.1 j k).continuous
  have hskew := hgood.mono fun ω h i => (h i).2.2.1
  have hproj := carverS_flux_block_skew_local_oscillation Q S hcont hskew
  obtain ⟨N, hNsub, hN, hNnull⟩ := exists_measurable_superset_of_null (ae_iff.mp hproj)
  refine ⟨φ, S, hgood, ?_, ?_⟩
  · intro r hr z
    obtain ⟨E, hE, hEtail, hEp⟩ := hosc r hr z
    refine ⟨E ∩ Nᶜ, hE.inter hN.compl, ?_, ?_⟩
    · calc
        reducedLaw Q (E ∩ Nᶜ)ᶜ = reducedLaw Q (Eᶜ ∪ N) := by
          rw [Set.compl_inter, compl_compl]
        _ ≤ reducedLaw Q Eᶜ + reducedLaw Q N := measure_union_le _ _
        _ = reducedLaw Q Eᶜ := by rw [hNnull, add_zero]
        _ ≤ _ := hEtail
    · rintro ω ⟨hωE, hωN⟩
      have hωproj := mt (fun h => hNsub h) hωN
      simp only [Set.mem_ofPred_eq, not_not] at hωproj
      obtain ⟨a, b, hab⟩ := hEp ω hωE
      refine ⟨a, fun i j k => (b i j k - b i k j) / 2,
        fun i => (hωproj i (b i) z (C * r)).1, ?_⟩
      apply le_trans ?_ hab
      exact Finset.sum_le_sum fun i _ => add_le_add le_rfl
        (hωproj i (b i) z (C * r)).2
  · intro hQ' β a μ hβ ha hμ ζ P Pdag hP hT ν
    exact fluxId_endpoint hd Q hQ' S
      (hgood.mono fun ω h i =>
        ⟨(h i).2.1, (h i).2.2.1, (h i).2.2.2.mono fun x hx => hx.2⟩) φ
      (hgood.mono fun ω h i =>
        ⟨(h i).1, (h i).2.2.2.mono fun x hx j => hx.1 j⟩)
      (fluxId_reduced_regular D Q hQ') β a μ hβ ha hμ ζ P Pdag hP hT ν

/-- Exact parabolic dilation of the actual unforced kernel at every coordinate order. -/
theorem carverS_flux_block_derivative_scale {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (k : ℕ) (dirs : Fin k → Fin d) (x : Vec d) :
    iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i s hs 0) x
        (fun j => unitVector (dirs j)) =
      (s ^ (-(d : ℝ) / 2) * (Real.sqrt s)⁻¹ ^ k) •
        iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i 1 zero_lt_one 0)
          ((Real.sqrt s)⁻¹ • x) (fun j => unitVector (dirs j)) := by
  let K := homogenizedGaussianSchwartz Q i 1 zero_lt_one (by norm_num) le_rfl 0
  let A : Vec d →L[ℝ] Vec d := (Real.sqrt s)⁻¹ • ContinuousLinearMap.id ℝ (Vec d)
  have hK : (K : Vec d → ℂ) = homogenizedGaussianKernel Q i 1 zero_lt_one 0 :=
    funext (homogenizedGaussianSchwartz_apply Q i 1 zero_lt_one (by norm_num) le_rfl 0)
  have he : homogenizedGaussianKernel Q i s hs 0 =
      s ^ (-(d : ℝ) / 2) • ((K : Vec d → ℂ) ∘ A) := by
    ext y
    simpa only [Pi.smul_apply, Function.comp_apply, A, smul_apply,
      ContinuousLinearMap.id_apply, hK] using homogenizedGaussianKernel_zero_scale Q i s hs y
  rw [he, iteratedFDeriv_const_smul_apply ((K.smooth k).comp A.contDiff).contDiffAt,
    A.iteratedFDeriv_comp_right (K.smooth k) x le_rfl]
  simp only [smul_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, A,
    ContinuousLinearMap.id_apply]
  rw [ContinuousMultilinearMap.map_smul_univ]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_smul, hK]

private theorem carverS_polynomial_gaussian_absorption {K r : ℝ}
    (hK : 0 < K) (hr : 0 ≤ r) (k : ℕ) :
    (1 + r) ^ k * Real.exp (-r ^ 2 / (4 * K)) ≤
      Real.exp (2 * K * (k : ℝ) ^ 2) * Real.exp (-r ^ 2 / (8 * K)) := by
  have hp : (1 + r) ^ k ≤ Real.exp ((k : ℝ) * r) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp r]) k
  have hq : (k : ℝ) * r - r ^ 2 / (4 * K) ≤
      2 * K * (k : ℝ) ^ 2 - r ^ 2 / (8 * K) := by
    apply (mul_le_mul_iff_right₀ (by positivity : 0 < 8 * K)).mp
    field_simp
    nlinarith only [sq_nonneg (r - 4 * K * (k : ℝ))]
  calc
    _ ≤ Real.exp ((k : ℝ) * r) * Real.exp (-r ^ 2 / (4 * K)) :=
      mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le
    _ = Real.exp ((k : ℝ) * r - r ^ 2 / (4 * K)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (2 * K * (k : ℝ) ^ 2 - r ^ 2 / (8 * K)) := Real.exp_le_exp.mpr hq
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- Every derivative of the actual anisotropic Gaussian has one structural
Gaussian envelope. Its width is chosen before the derivative order and law. -/
theorem carverS_flux_block_gaussian_envelope (d : ℕ) (D : StructuralData d) :
    ∃ Cenv : ℝ, ∃ Cder : ℕ → ℝ, 1 ≤ Cenv ∧ (∀ k, 1 ≤ Cder k) ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (i : Fin d)
      (s : ℝ) (hs : 0 < s) (k : ℕ) (dirs : Fin k → Fin d) (x : Vec d),
      ‖iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i s hs 0) x
        (fun j => unitVector (dirs j))‖ ≤
      Cder k * s ^ (-(k : ℝ) / 2) *
        (s ^ (-(d : ℝ) / 2) * Real.exp (-euclideanNorm x ^ 2 / (Cenv * s))) := by
  let K := sourceReducedBound D.ellipticity
  let F := 1 + 2 * (d : ℝ) ^ 2 * K
  let P := Real.sqrt ((Fintype.card (Equiv.Perm (Fin d)) : ℝ) * K ^ d)
  have hKone : 1 ≤ K := by
    have he : 1 ≤ Real.exp (2 * D.ellipticity) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith [D.one_le_ellipticity])
    have hp : 1 ≤ 3 * D.ellipticity ^ 2 + D.ellipticity + 1 := by
      nlinarith [sq_nonneg D.ellipticity, D.one_le_ellipticity]
    exact one_le_mul_of_one_le_of_one_le he hp
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one hKone
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hP : 0 ≤ P := Real.sqrt_nonneg _
  let A := fun k : ℕ => (2 : ℝ) ^ (k ^ 2) * F ^ k * P *
    Real.exp (2 * K * (k : ℝ) ^ 2)
  have hA (k : ℕ) : 0 ≤ A k := by dsimp [A]; positivity
  refine ⟨8 * K, fun k => A k + 1, by linarith, fun k => by linarith [hA k], ?_⟩
  have hunit (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (i : Fin d)
      (k : ℕ) (dirs : Fin k → Fin d) (x : Vec d) :
      ‖iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i 1 zero_lt_one 0) x
        (fun j => unitVector (dirs j))‖ ≤
        (A k + 1) * Real.exp (-euclideanNorm x ^ 2 / (8 * K)) := by
    have hxnorm : 0 ≤ euclideanNorm x := Real.sqrt_nonneg _
    let L := iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i 1 zero_lt_one 0) x
    have heval : ‖L (fun j => unitVector (dirs j))‖ ≤ ‖L‖ := by
      have hh := L.le_opNorm (fun j => unitVector (dirs j))
      exact hh.trans (mul_le_of_le_one_right (norm_nonneg L)
        (Finset.prod_le_one₀ (fun j _ => norm_nonneg _) fun j _ =>
          (norm_vec_le_euclideanNorm _).trans (euclideanNorm_unitVector_eq_one _).le))
    have hder := norm_iteratedFDeriv_homogenizedGaussianKernel_le Q i 1 zero_lt_one
      (by norm_num) 0 x k
    have hgauss := norm_homogenizedGaussianKernel_le_gaussian Q i 1 zero_lt_one
      (by norm_num) le_rfl 0 x
    simp only [norm_zero, add_zero, mul_one, zero_pow (by decide : 2 ≠ 0),
      mul_zero, zero_sub, ← neg_div] at hder hgauss
    change ‖L‖ ≤ (2 : ℝ) ^ (k ^ 2) * (F * (1 + euclideanNorm x)) ^ k *
      ‖homogenizedGaussianKernel Q i 1 zero_lt_one 0 x‖ at hder
    change ‖homogenizedGaussianKernel Q i 1 zero_lt_one 0 x‖ ≤
      P * Real.exp (-euclideanNorm x ^ 2 / (4 * K)) at hgauss
    calc
      _ ≤ (2 : ℝ) ^ (k ^ 2) * (F * (1 + euclideanNorm x)) ^ k *
          (P * Real.exp (-euclideanNorm x ^ 2 / (4 * K))) :=
        heval.trans (hder.trans (mul_le_mul_of_nonneg_left hgauss (by positivity)))
      _ = ((2 : ℝ) ^ (k ^ 2) * F ^ k * P) *
          ((1 + euclideanNorm x) ^ k * Real.exp (-euclideanNorm x ^ 2 / (4 * K))) := by
        rw [mul_pow]
        ring
      _ ≤ ((2 : ℝ) ^ (k ^ 2) * F ^ k * P) *
          (Real.exp (2 * K * (k : ℝ) ^ 2) * Real.exp (-euclideanNorm x ^ 2 / (8 * K))) :=
        mul_le_mul_of_nonneg_left
          (carverS_polynomial_gaussian_absorption hK (Real.sqrt_nonneg _) k) (by positivity)
      _ = A k * Real.exp (-euclideanNorm x ^ 2 / (8 * K)) := by dsimp [A]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  intro Q i s hs k dirs x
  have hscale := carverS_flux_block_derivative_scale Q i s hs k dirs x
  have hpow : (Real.sqrt s)⁻¹ ^ k = s ^ (-(k : ℝ) / 2) := by
    rw [← Real.rpow_natCast, Real.sqrt_eq_rpow, ← Real.rpow_neg hs.le,
      ← Real.rpow_mul hs.le]
    congr 1
    ring
  have hnorm : euclideanNorm ((Real.sqrt s)⁻¹ • x) ^ 2 = euclideanNorm x ^ 2 / s := by
    rw [TimeChange.euclideanNorm_smul, abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr hs)),
      mul_pow, inv_pow, Real.sq_sqrt hs.le]
    ring
  rw [hscale, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    _ ≤ (s ^ (-(d : ℝ) / 2) * (Real.sqrt s)⁻¹ ^ k) *
        ((A k + 1) * Real.exp (-euclideanNorm ((Real.sqrt s)⁻¹ • x) ^ 2 / (8 * K))) :=
      mul_le_mul_of_nonneg_left (hunit Q i k dirs _) (by positivity)
    _ = _ := by
      rw [hpow, hnorm]
      have he : -(euclideanNorm x ^ 2 / s) / (8 * K) =
          -euclideanNorm x ^ 2 / (8 * K * s) := by ring
      rw [he]
      ring

/-- The spatial Gaussian supremum in the block statement is finite and controls
the same Gaussian at every point of the prescribed closed Euclidean ball. -/
theorem carverS_flux_block_gaussian_spatial_sup {d : ℕ} (s : ℝ) (hs : 0 < s)
    (Cenv : ℝ) (x z : Vec d) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    let w := fun y : Vec d => s ^ (-(d : ℝ) / 2) *
      Real.exp (-euclideanNorm (x - y) ^ 2 / (Cenv * s))
    let B := {y : Vec d | euclideanNorm (y - z) ≤ ρ}
    BddAbove (w '' B) ∧ 0 ≤ sSup (w '' B) ∧ ∀ y ∈ B, w y ≤ sSup (w '' B) := by
  intro w B
  have hw : Continuous w := by
    apply continuous_const.mul
    apply Real.continuous_exp.comp
    exact (((Entropy.continuous_euclideanNorm'.comp
      (continuous_const.sub continuous_id)).pow 2).neg).div_const _
  have hB : IsCompact B := isCompact_physical_euclidean_closedBall z ρ
  have hb : BddAbove (w '' B) := hB.bddAbove_image hw.continuousOn
  have hz : z ∈ B := by
    simpa [B, euclideanNorm, euclideanSq, dot] using hρ
  refine ⟨hb, ?_, fun y hy => le_csSup hb ⟨y, hy, rfl⟩⟩
  exact le_trans (by dsimp [w]; positivity) (le_csSup hb ⟨z, hz, rfl⟩)

private theorem carverS_norm_integral_le_l2_product {α : Type*}
    [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ} {h : α → ℂ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᵐ x ∂μ, ‖h x‖ ≤ C * f x * g x) :
    ‖∫ x, h x ∂μ‖ ≤ C * Calculus.S1.l2Size μ f * Calculus.S1.l2Size μ g := by
  calc
    _ ≤ ∫ x, C * (f x * g x) ∂μ :=
      norm_integral_le_of_norm_le ((hf.integrable_mul hg).const_mul C)
        (hb.mono fun x hx => by simpa only [mul_assoc] using hx)
    _ = C * ∫ x, f x * g x ∂μ := integral_const_mul _ _
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (Calculus.S1.integral_mul_le_l2Size_real hf hg) hC

private theorem carverS_norm_sum_mul_le {d : ℕ} (u v : Fin d → ℂ)
    {M N : ℝ} (hM : 0 ≤ M) (hu : ∀ j, ‖u j‖ ≤ M) (hv : ∀ j, ‖v j‖ ≤ N) :
    ‖∑ j, u j * v j‖ ≤ (d : ℝ) * M * N := by
  calc
    _ ≤ ∑ j : Fin d, ‖u j * v j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin d, M * N := Finset.sum_le_sum fun j _ => by
      rw [norm_mul]
      exact mul_le_mul (hu j) (hv j) (norm_nonneg _) hM
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]; ring

private theorem carverS_norm_matrix_test_le {d : ℕ}
    (a : Fin d → Fin d → ℂ) (v w : Fin d → ℂ) {M N B : ℝ}
    (hM : 0 ≤ M) (hN : 0 ≤ N) (ha : ∀ k j, ‖a k j‖ ≤ M)
    (hv : ∀ j, ‖v j‖ ≤ N) (hw : ∀ j, ‖w j‖ ≤ B) :
    ‖∑ k, (∑ j, a k j * v j) * w k‖ ≤ (d : ℝ) ^ 2 * M * B * N := by
  have hh := carverS_norm_sum_mul_le (fun k => ∑ j, a k j * v j) w
    (by positivity : 0 ≤ (d : ℝ) * M * N)
    (fun k => carverS_norm_sum_mul_le (a k) v hM (ha k) hv) hw
  convert hh using 1; ring

private theorem carverS_norm_component_le_energy {d : ℕ} (v : Fin d → ℂ) (j : Fin d) :
    ‖v j‖ ≤ Real.sqrt (∑ k : Fin d, ‖v k‖ ^ 2) := by
  simpa only [abs_norm] using Real.abs_le_sqrt
    (Finset.single_le_sum (fun k _ => sq_nonneg ‖v k‖) (Finset.mem_univ j))

private theorem carverS_abs_entry_le_frobeniusNorm {d : ℕ} (S : Mat d) (i j : Fin d) :
    |S i j| ≤ frobeniusNorm S := by
  unfold frobeniusNorm
  apply Real.abs_le_sqrt
  rw [sq]
  exact (Finset.single_le_sum (f := fun k => S i k * S i k)
    (fun k _ => mul_self_nonneg _) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun k => ∑ l, S k l * S k l)
      (fun k _ => Finset.sum_nonneg fun l _ => mul_self_nonneg _) (Finset.mem_univ i))

/-- Spatial Cauchy--Schwarz for the four literal endpoint identity terms.
The two corrector sizes remain separate, so the source good-event bound can
control their sum using the same selected corrector pair and centers. -/
theorem carverS_flux_block_identity_l2_bound {d : ℕ} (μ : Measure (Vec d))
    (φ : Vec d → ℝ) (S : Vec d → Mat d) (a : Vec d → Fin d → Fin d → ℝ)
    (F g : Vec d → Fin d → ℂ) (q ψ : Vec d → ℂ) (ζ : ℂ) (i : Fin d)
    (hφ : MemLp φ 2 μ) (hS : MemLp (fun x => frobeniusNorm (S x)) 2 μ)
    (hq : MemLp q 2 μ)
    (hF : MemLp (fun x => Real.sqrt (∑ j : Fin d, ‖F x j‖ ^ 2)) 2 μ)
    (hg : MemLp (fun x => Real.sqrt (∑ j : Fin d, ‖g x j‖ ^ 2)) 2 μ)
    (A B M : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (ha : ∀ᵐ x ∂μ, ∀ k j, |a x k j| ≤ M)
    (hψ : ∀ᵐ x ∂μ, ‖ψ x‖ ≤ A)
    (hDψ : ∀ᵐ x ∂μ, ∀ k : Fin d, ‖fderiv ℝ ψ x (unitVector k)‖ ≤ B) :
    ‖(∫ x, (φ x : ℂ) * q x * ψ x ∂μ) +
      (∫ x, (φ x : ℂ) * (∑ k : Fin d,
        (∑ j : Fin d, (a x k j : ℂ) * F x j) *
          fderiv ℝ ψ x (unitVector k)) ∂μ) -
      (∫ x, ∑ k : Fin d, ∑ j : Fin d, (S x k j : ℂ) * F x j *
        fderiv ℝ ψ x (unitVector k) ∂μ) +
      2 * ζ * (∫ x, (∑ k : Fin d, (S x k i : ℂ) * g x k) * ψ x ∂μ)‖ ≤
      Calculus.S1.l2Size μ φ *
        (A * Calculus.S1.l2Size μ q + (d : ℝ) ^ 2 * M * B *
          Calculus.S1.l2Size μ (fun x => Real.sqrt (∑ j : Fin d, ‖F x j‖ ^ 2))) +
      Calculus.S1.l2Size μ (fun x => frobeniusNorm (S x)) *
        ((d : ℝ) ^ 2 * B *
          Calculus.S1.l2Size μ (fun x => Real.sqrt (∑ j : Fin d, ‖F x j‖ ^ 2)) +
          2 * ‖ζ‖ * (d : ℝ) * A *
            Calculus.S1.l2Size μ (fun x => Real.sqrt (∑ j : Fin d, ‖g x j‖ ^ 2))) := by
  have hφabs : MemLp (fun x => |φ x|) 2 μ := by
    simpa only [Real.norm_eq_abs] using hφ.norm
  have hφsize : Calculus.S1.l2Size μ (fun x => |φ x|) = Calculus.S1.l2Size μ φ := by
    simpa only [Real.norm_eq_abs] using Calculus.S1.l2Size_norm (μ := μ) φ
  have hvalue := carverS_norm_integral_le_l2_product hφabs hq.norm hA (hψ.mono
    fun x hx => show ‖(φ x : ℂ) * q x * ψ x‖ ≤ A * |φ x| * ‖q x‖ from by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      nlinarith only [mul_le_mul_of_nonneg_left hx
        (mul_nonneg (abs_nonneg (φ x)) (norm_nonneg (q x)))])
  rw [hφsize, Calculus.S1.l2Size_norm] at hvalue
  have hfirst : ‖∫ x, (φ x : ℂ) * (∑ k : Fin d,
      (∑ j : Fin d, (a x k j : ℂ) * F x j) *
        fderiv ℝ ψ x (unitVector k)) ∂μ‖ ≤
      ((d : ℝ) ^ 2 * M * B) * Calculus.S1.l2Size μ φ *
        Calculus.S1.l2Size μ (fun x => Real.sqrt (∑ j : Fin d, ‖F x j‖ ^ 2)) := by
    have hh := carverS_norm_integral_le_l2_product hφabs hF
      (h := fun x => (φ x : ℂ) * (∑ k : Fin d,
        (∑ j : Fin d, (a x k j : ℂ) * F x j) *
          fderiv ℝ ψ x (unitVector k)))
      (by positivity : 0 ≤ (d : ℝ) ^ 2 * M * B) ?_
    · simpa only [hφsize] using hh
    filter_upwards [ha, hDψ] with x hax hDx
    have hm := carverS_norm_matrix_test_le (fun k j => (a x k j : ℂ)) (F x)
      (fun k => fderiv ℝ ψ x (unitVector k)) hM (Real.sqrt_nonneg _)
      (fun k j => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hax k j)
      (carverS_norm_component_le_energy (F x)) hDx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    nlinarith only [mul_le_mul_of_nonneg_left hm (abs_nonneg (φ x))]
  have hsecond : ‖∫ x, ∑ k : Fin d, ∑ j : Fin d, (S x k j : ℂ) * F x j *
      fderiv ℝ ψ x (unitVector k) ∂μ‖ ≤
      ((d : ℝ) ^ 2 * B) * Calculus.S1.l2Size μ (fun x => frobeniusNorm (S x)) *
        Calculus.S1.l2Size μ (fun x => Real.sqrt (∑ j : Fin d, ‖F x j‖ ^ 2)) := by
    apply carverS_norm_integral_le_l2_product hS hF (by positivity)
    filter_upwards [hDψ] with x hDx
    have hm := carverS_norm_matrix_test_le (fun k j => (S x k j : ℂ)) (F x)
      (fun k => fderiv ℝ ψ x (unitVector k))
      (show 0 ≤ frobeniusNorm (S x) from Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      (fun k j => by simpa only [Complex.norm_real, Real.norm_eq_abs] using
        carverS_abs_entry_le_frobeniusNorm (S x) k j)
      (carverS_norm_component_le_energy (F x)) hDx
    simp only [Finset.sum_mul] at hm
    nlinarith only [hm]
  have hthird : ‖∫ x, (∑ k : Fin d, (S x k i : ℂ) * g x k) * ψ x ∂μ‖ ≤
      ((d : ℝ) * A) * Calculus.S1.l2Size μ (fun x => frobeniusNorm (S x)) *
        Calculus.S1.l2Size μ (fun x => Real.sqrt (∑ j : Fin d, ‖g x j‖ ^ 2)) := by
    apply carverS_norm_integral_le_l2_product hS hg (by positivity)
    filter_upwards [hψ] with x hx
    have hm := carverS_norm_sum_mul_le (fun k => (S x k i : ℂ)) (g x)
      (show 0 ≤ frobeniusNorm (S x) from Real.sqrt_nonneg _)
      (fun k => by simpa only [Complex.norm_real, Real.norm_eq_abs] using
        carverS_abs_entry_le_frobeniusNorm (S x) k i)
      (carverS_norm_component_le_energy (g x))
    rw [norm_mul]
    have hsx : 0 ≤ frobeniusNorm (S x) := Real.sqrt_nonneg _
    have hh := mul_le_mul hm hx (norm_nonneg _) (by positivity :
      0 ≤ (d : ℝ) * frobeniusNorm (S x) * Real.sqrt (∑ j : Fin d, ‖g x j‖ ^ 2))
    nlinarith only [hh]
  have hlast := mul_le_mul_of_nonneg_left hthird (by positivity : 0 ≤ 2 * ‖ζ‖)
  calc
    _ ≤ (‖∫ x, (φ x : ℂ) * q x * ψ x ∂μ‖ +
        ‖∫ x, (φ x : ℂ) * (∑ k : Fin d,
          (∑ j : Fin d, (a x k j : ℂ) * F x j) *
            fderiv ℝ ψ x (unitVector k)) ∂μ‖) +
        ‖∫ x, ∑ k : Fin d, ∑ j : Fin d, (S x k j : ℂ) * F x j *
          fderiv ℝ ψ x (unitVector k) ∂μ‖ +
        ‖2 * ζ * (∫ x, (∑ k : Fin d, (S x k i : ℂ) * g x k) * ψ x ∂μ)‖ :=
      (norm_add_le _ _).trans (add_le_add
        ((norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ _ := by
      rw [norm_mul, norm_mul, Complex.norm_two]
      nlinarith only [hvalue, hfirst, hsecond, hlast]

/-- Passing from the literal spatial L² size to a normalized ball average
retains exactly the square root of its volume. -/
theorem carverS_flux_block_l2Size_normalized {α 𝕜 : Type*} [MeasurableSpace α]
    [RCLike 𝕜] (μ : Measure α) (hμ : 0 < μ.real Set.univ) (f : α → 𝕜) :
    Calculus.S1.l2Size μ f = Real.sqrt (μ.real Set.univ) *
      Real.sqrt ((μ.real Set.univ)⁻¹ * ∫ x, ‖f x‖ ^ 2 ∂μ) := by
  unfold Calculus.S1.l2Size
  rw [← Real.sqrt_mul hμ.le, ← mul_assoc, mul_inv_cancel₀ hμ.ne', one_mul]

private theorem carverS_continuous_memLp_ball {d : ℕ} {𝕜 : Type*} [RCLike 𝕜]
    (f : Vec d → 𝕜) (hf : Continuous f) (z : Vec d) (ρ : ℝ) :
    MemLp f 2 (volume.restrict {x : Vec d | euclideanNorm (x - z) < ρ}) := by
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable.restrict).mpr
  exact (ContinuousOn.integrableOn_compact
    (isCompact_physical_euclidean_closedBall z ρ)
    (hf.norm.pow 2).continuousOn).mono_set (fun x hx =>
      show euclideanNorm (x - z) ≤ ρ from
        (show euclideanNorm (x - z) < ρ from hx).le)

/-- The literal source oscillation bound controls each selected centered pair
in spatial L². Smoothness discharges both local `MemLp` obligations. -/
theorem carverS_flux_block_centered_corrector_l2 {d : ℕ}
    (φ : Fin d → Vec d → ℝ) (S : Fin d → Vec d → Mat d)
    (a : Fin d → ℝ) (b : Fin d → Mat d)
    (hφ : ∀ i, Continuous (φ i))
    (hS : ∀ i j k, Continuous (fun x => S i x j k))
    (z : Vec d) (ρ : ℝ) (hρ : 0 < ρ) (H : ℝ)
    (hosc : (∑ i : Fin d,
      (Real.sqrt ((volume {x : Vec d | euclideanNorm (x - z) < ρ}).toReal⁻¹ *
        ∫ x in {x : Vec d | euclideanNorm (x - z) < ρ}, |φ i x - a i| ^ 2) +
       Real.sqrt ((volume {x : Vec d | euclideanNorm (x - z) < ρ}).toReal⁻¹ *
        ∫ x in {x : Vec d | euclideanNorm (x - z) < ρ},
          frobeniusNorm (S i x - b i) ^ 2))) ≤ H) :
    let m := volume.restrict {x : Vec d | euclideanNorm (x - z) < ρ}
    ∀ i : Fin d,
      MemLp (fun x => φ i x - a i) 2 m ∧
      MemLp (fun x => frobeniusNorm (S i x - b i)) 2 m ∧
      Calculus.S1.l2Size m (fun x => φ i x - a i) +
        Calculus.S1.l2Size m (fun x => frobeniusNorm (S i x - b i)) ≤
          Real.sqrt ((volume {x : Vec d | euclideanNorm (x - z) < ρ}).toReal) * H := by
  dsimp only
  intro i
  have hcφ : Continuous (fun x => φ i x - a i) := (hφ i).sub continuous_const
  have hcS : Continuous (fun x => frobeniusNorm (S i x - b i)) := by
    unfold frobeniusNorm frobeniusSq
    apply Real.continuous_sqrt.comp
    exact continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ =>
      ((hS i j k).sub continuous_const).mul ((hS i j k).sub continuous_const)
  refine ⟨carverS_continuous_memLp_ball _ hcφ z ρ,
    carverS_continuous_memLp_ball _ hcS z ρ, ?_⟩
  have hv : 0 < (volume.restrict
      {x : Vec d | euclideanNorm (x - z) < ρ}).real Set.univ := by
    simpa only [measureReal_restrict_apply_univ] using localSpatialEnergy_window_volume z ρ hρ
  rw [carverS_flux_block_l2Size_normalized _ hv,
    carverS_flux_block_l2Size_normalized _ hv, ← mul_add]
  simp only [measureReal_restrict_apply_univ, Real.norm_eq_abs, sq_abs]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  have hcomponent := (Finset.single_le_sum
    (f := fun j : Fin d =>
      Real.sqrt ((volume {x : Vec d | euclideanNorm (x - z) < ρ}).toReal⁻¹ *
        ∫ x in {x : Vec d | euclideanNorm (x - z) < ρ}, |φ j x - a j| ^ 2) +
      Real.sqrt ((volume {x : Vec d | euclideanNorm (x - z) < ρ}).toReal⁻¹ *
        ∫ x in {x : Vec d | euclideanNorm (x - z) < ρ},
          frobeniusNorm (S j x - b j) ^ 2))
    (fun j _ => add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (Finset.mem_univ i)).trans hosc
  simpa only [sq_abs, measureReal_def] using hcomponent

/-- All four literal endpoint identity terms may be restricted to a spatial
window containing the test's topological support. The derivative terms have
the same support inclusion. -/
theorem carverS_flux_block_identity_localization {d : ℕ}
    (E : Set (Vec d)) (φ : Vec d → ℝ) (S : Vec d → Mat d)
    (a : Vec d → Mat d) (F g : Vec d → Fin d → ℂ)
    (q ψ : Vec d → ℂ) (ζ : ℂ) (i : Fin d) (hψ : tsupport ψ ⊆ E) :
    (∫ x, (φ x : ℂ) * q x * ψ x) +
      (∫ x, (φ x : ℂ) * (∑ k : Fin d,
        (∑ j : Fin d, (a x k j : ℂ) * F x j) *
          fderiv ℝ ψ x (unitVector k))) -
      (∫ x, ∑ k : Fin d, ∑ j : Fin d, (S x k j : ℂ) * F x j *
        fderiv ℝ ψ x (unitVector k)) +
      2 * ζ * (∫ x, (∑ k : Fin d, (S x k i : ℂ) * g x k) * ψ x) =
    (∫ x in E, (φ x : ℂ) * q x * ψ x) +
      (∫ x in E, (φ x : ℂ) * (∑ k : Fin d,
        (∑ j : Fin d, (a x k j : ℂ) * F x j) *
          fderiv ℝ ψ x (unitVector k))) -
      (∫ x in E, ∑ k : Fin d, ∑ j : Fin d, (S x k j : ℂ) * F x j *
        fderiv ℝ ψ x (unitVector k)) +
      2 * ζ * (∫ x in E, (∑ k : Fin d, (S x k i : ℂ) * g x k) * ψ x) := by
  have hz (x : Vec d) (hx : x ∉ E) : ψ x = 0 := by
    by_contra h
    exact hx (hψ (subset_tsupport ψ h))
  have hDz (x : Vec d) (hx : x ∉ E) : fderiv ℝ ψ x = 0 := by
    by_contra h
    exact hx (hψ (support_fderiv_subset ℝ h))
  have h0 := setIntegral_eq_integral_of_forall_compl_eq_zero
    (μ := (volume : Measure (Vec d))) (s := E)
    (f := fun x => (φ x : ℂ) * q x * ψ x) (fun x hx => by simp [hz x hx])
  have h1 := setIntegral_eq_integral_of_forall_compl_eq_zero
    (μ := (volume : Measure (Vec d))) (s := E)
    (f := fun x => (φ x : ℂ) * (∑ k : Fin d,
      (∑ j : Fin d, (a x k j : ℂ) * F x j) * fderiv ℝ ψ x (unitVector k)))
    (fun x hx => by simp [hDz x hx])
  have h2 := setIntegral_eq_integral_of_forall_compl_eq_zero
    (μ := (volume : Measure (Vec d))) (s := E)
    (f := fun x => ∑ k : Fin d, ∑ j : Fin d, (S x k j : ℂ) * F x j *
      fderiv ℝ ψ x (unitVector k)) (fun x hx => by simp [hDz x hx])
  have h3 := setIntegral_eq_integral_of_forall_compl_eq_zero
    (μ := (volume : Measure (Vec d))) (s := E)
    (f := fun x => (∑ k : Fin d, (S x k i : ℂ) * g x k) * ψ x)
    (fun x hx => by simp [hz x hx])
  rw [h0, h1, h2, h3]

/-- The root cutoff window lies strictly inside the source window at
radius `(R + 1) * r`, even when the source enlargement constant is one. -/
theorem carverS_flux_block_cutoff_test_support {d : ℕ}
    (χ : Vec d → ℝ) (kernel : Vec d → ℂ) (x z : Vec d)
    (R r C : ℝ) (hR : 0 ≤ R) (hr : 0 < r) (hC : 1 ≤ C)
    (hχ : Function.support χ ⊆ {y : Vec d | euclideanNorm y ≤ R * r}) :
    tsupport (fun y : Vec d => (χ (y - z) : ℂ) * kernel (x - y)) ⊆
      {y : Vec d | euclideanNorm (y - z) < C * ((R + 1) * r)} := by
  have hn : Continuous (fun y : Vec d => euclideanNorm (y - z)) := by
    unfold euclideanNorm euclideanSq dot
    fun_prop
  have hs : Function.support (fun y : Vec d => (χ (y - z) : ℂ) * kernel (x - y)) ⊆
      {y : Vec d | euclideanNorm (y - z) ≤ R * r} := by
    intro y hy
    by_contra h
    have hc : χ (y - z) = 0 := by
      by_contra hc
      exact h (hχ hc)
    exact hy (by simp only [hc, Complex.ofReal_zero, zero_mul])
  have hsub := closure_minimal hs (isClosed_le hn continuous_const)
  intro y hy
  have hsmall : euclideanNorm (y - z) ≤ R * r := hsub hy
  have hlarge := mul_le_mul_of_nonneg_right hC
    (mul_nonneg (by linarith : 0 ≤ R + 1) hr.le)
  change euclideanNorm (y - z) < C * ((R + 1) * r)
  exact hsmall.trans_lt ((show R * r < (R + 1) * r by nlinarith).trans_le
    (by simpa only [one_mul] using hlarge))

/-- The actual local-time energy controls both spatial L² factors on the
same window, using the fixed gradient and time-derivative representatives. -/
theorem carverS_flux_block_spatial_energy_l2 {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (t : ℝ≥0)
    (ρ : ℝ) (hρ : 0 < ρ) (z : Vec d)
    (G : Fin d → Lp ℂ 2 (reducedLaw Q)) (V : Lp ℂ 2 (reducedLaw Q)) :
    let m := volume.restrict {x : Vec d | euclideanNorm (x - z) < ρ}
    ∀ᵐ ω ∂reducedLaw Q,
      MemLp (fun x => Real.sqrt (∑ j : Fin d, ‖G j (translate x ω)‖ ^ 2)) 2 m ∧
      MemLp (fun x => V (translate x ω)) 2 m ∧
      Calculus.S1.l2Size m
          (fun x => Real.sqrt (∑ j : Fin d, ‖G j (translate x ω)‖ ^ 2)) ≤
        Real.sqrt (volume.real {x : Vec d | euclideanNorm (x - z) < ρ}) *
          localSpatialEnergy Q t ρ hρ z G V ω ∧
      Real.sqrt (t : ℝ) * Calculus.S1.l2Size m (fun x => V (translate x ω)) ≤
        Real.sqrt (volume.real {x : Vec d | euclideanNorm (x - z) < ρ}) *
          localSpatialEnergy Q t ρ hρ z G V ω := by
  dsimp only
  let := reducedLaw_probability Q
  have hv := localSpatialEnergy_window_volume z ρ hρ
  have hfin := (ENNReal.toReal_pos_iff.mp hv).2.ne
  have hVI := ae_integrableOn_stationary_orbit (reducedLaw_stationary Q)
    ((Lp.stronglyMeasurable V).measurable.norm.pow_const 2)
    ((Lp.memLp V).integrable_norm_pow (by norm_num)) hfin
  filter_upwards [ae_integrableOn_localSpatialEnergy_integrand Q (t : ℝ) G V hfin,
    hVI] with ω hI hV
  have htr : Measurable (fun x : Vec d => translate x ω) :=
    (Probability.continuous_translate.comp (continuous_id.prodMk continuous_const)).measurable
  have hmV := (Lp.stronglyMeasurable V).measurable.comp htr
  have hmG : Measurable (fun x : Vec d => ∑ j : Fin d, ‖G j (translate x ω)‖ ^ 2) :=
    Finset.measurable_sum _ fun j _ =>
      ((Lp.stronglyMeasurable (G j)).measurable.comp htr).norm.pow_const 2
  have hGI : IntegrableOn (fun x : Vec d => ∑ j : Fin d,
      ‖G j (translate x ω)‖ ^ 2) {x : Vec d | euclideanNorm (x - z) < ρ} := by
    apply hI.mono' hmG.aestronglyMeasurable.restrict
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
      exact le_add_of_nonneg_right (mul_nonneg t.property (sq_nonneg _))
  have hGsquare (x : Vec d) :
      ‖Real.sqrt (∑ j : Fin d, ‖G j (translate x ω)‖ ^ 2)‖ ^ 2 =
        ∑ j : Fin d, ‖G j (translate x ω)‖ ^ 2 := by
    rw [Real.norm_eq_abs, sq_abs, Real.sq_sqrt
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  have hGM : MemLp (fun x : Vec d =>
      Real.sqrt (∑ j : Fin d, ‖G j (translate x ω)‖ ^ 2)) 2
      (volume.restrict {x : Vec d | euclideanNorm (x - z) < ρ}) := by
    apply (memLp_two_iff_integrable_sq_norm hmG.sqrt.aestronglyMeasurable.restrict).mpr
    exact hGI.integrable.congr
      (Filter.Eventually.of_forall fun x => (hGsquare x).symm)
  have hVM : MemLp (fun x : Vec d => V (translate x ω)) 2
      (volume.restrict {x : Vec d | euclideanNorm (x - z) < ρ}) :=
    (memLp_two_iff_integrable_sq_norm hmV.aestronglyMeasurable.restrict).mpr hV
  have hE :
      Real.sqrt (volume.real {x : Vec d | euclideanNorm (x - z) < ρ}) *
        localSpatialEnergy Q t ρ hρ z G V ω =
      Real.sqrt (∫ x in {x : Vec d | euclideanNorm (x - z) < ρ},
        (∑ j : Fin d, ‖G j (translate x ω)‖ ^ 2) +
          (t : ℝ) * ‖V (translate x ω)‖ ^ 2) := by
    unfold localSpatialEnergy
    rw [average_eq, measureReal_restrict_apply_univ, smul_eq_mul,
      ← Real.sqrt_mul hv.le, ← mul_assoc, mul_inv_cancel₀ hv.ne', one_mul]
  refine ⟨hGM, hVM, ?_, ?_⟩
  · rw [hE]
    unfold Calculus.S1.l2Size
    simp only [hGsquare]
    apply Real.sqrt_le_sqrt
    exact integral_mono hGI hI (fun x =>
      le_add_of_nonneg_right (mul_nonneg t.property (sq_nonneg _)))
  · rw [hE]
    unfold Calculus.S1.l2Size
    have hmono := integral_mono (hV.const_mul (t : ℝ)) hI (fun x =>
      le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => sq_nonneg _))
    have hsqrt := Real.sqrt_le_sqrt hmono
    have ht : 0 ≤ (t : ℝ) := t.property
    simpa only [integral_const_mul, Real.sqrt_mul ht] using hsqrt

/-- The local-time dependency controls the gradient selected by the flux
identity and the actual derivative, by uniqueness of both witnesses. -/
theorem carverS_flux_block_local_time_on_flux_witness
    (hlt : node_e_u3A_local_u2D_timeStmt) (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) (p : ℝ) (hp : 2 ≤ p) :
    ∃ C Cp : ℝ, 1 ≤ C ∧ 0 < Cp ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
    ∀ G J : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ t : ℝ≥0, 0 < (t : ℝ) → IsEndpointWeakFlux hd Q ν ζ a
        (indexedEndpoint hd Q ν ζ P Pdag β a μ t) (G t) (J t)) →
    ∀ (t : ℝ≥0) (ht : 0 < (t : ℝ)),
      let V := deriv (fun r : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ r.toNNReal)
        (t : ℝ)
      ∀ (ρ : ℝ) (z : Vec d) (hρ : Real.sqrt (t : ℝ) ≤ ρ),
        MemLp (localSpatialEnergy Q t ρ (lt_of_lt_of_le (Real.sqrt_pos.mpr ht) hρ)
          z (G t) V) (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm (localSpatialEnergy Q t ρ
          (lt_of_lt_of_le (Real.sqrt_pos.mpr ht) hρ) z (G t) V)
          (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        C * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C * (t : ℝ) ^ (-(1 / 2 : ℝ)) *
          Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
          (eLpNorm (indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8) :
            FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  obtain ⟨C, Cp, hC, hCp, hlocal⟩ := hlt d hd D p hp
  refine ⟨C, Cp, hC, hCp, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν G J hflux t ht
  obtain ⟨H, W, hHW, hmoment⟩ := hlocal Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  have hG : G t = H t := (hflux t ht).1.unique (hHW t ht).1
  have hV := (hHW t ht).2.2.deriv
  dsimp only
  rw [hG, hV]
  exact (hmoment t ht).2

private theorem carverS_memLp_spatial_vector_energy {d : ℕ}
    (m : Measure (Vec d)) (f : Fin d → Vec d → ℂ)
    (hf : ∀ j, MemLp (f j) 2 m) :
    MemLp (fun x => Real.sqrt (∑ j : Fin d, ‖f j x‖ ^ 2)) 2 m := by
  have hI : Integrable (fun x => ∑ j : Fin d, ‖f j x‖ ^ 2) m :=
    integrable_finsetSum _ fun j _ => (hf j).integrable_norm_pow (by norm_num)
  have hm := Real.continuous_sqrt.comp_aestronglyMeasurable hI.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  exact hI.congr (Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [Real.norm_eq_abs, sq_abs, Real.sq_sqrt
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)])

/-- The literal shifted gradient and divergence in the endpoint identity
are locally L² for the actual fixed `Lp` representatives. Coefficient bounds
come from the reduced law, with no additional spatial integrability premise. -/
theorem carverS_flux_block_endpoint_fields_memLp {d : ℕ} (hd : 2 ≤ d)
    (D : StructuralData d) (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q) (ρ : ℝ) (hρ : 0 < ρ) (z : Vec d)
    (U V : Lp ℂ 2 (reducedLaw Q)) (G : Fin d → Lp ℂ 2 (reducedLaw Q))
    (ν : EndpointIndex d) (ζ c : ℂ) :
    let m := volume.restrict {x : Vec d | euclideanNorm (x - z) < ρ}
    ∀ᵐ ω ∂reducedLaw Q,
      let g := fun (x : Vec d) (j : Fin d) => G j (translate x ω)
      let u := fun x : Vec d => U (translate x ω)
      let v := fun x : Vec d => V (translate x ω)
      let F := fun (x : Vec d) (j : Fin d) => g x j -
        match ν with
        | .inr true => 2 * ζ * (unitVector (⟨0, by omega⟩ : Fin d) j : ℂ) * u x
        | _ => 0
      let q := fun x : Vec d => 2 * v x +
        match ν with
        | .inr true => 0
        | _ => 2 * c - 2 * ζ * (∑ k : Fin d,
            (ω.1 x k ⟨0, by omega⟩ : ℂ) * g x k)
      MemLp u 2 m ∧ MemLp v 2 m ∧
        (∀ j, MemLp (fun x => g x j) 2 m) ∧
        MemLp (fun x => Real.sqrt (∑ j : Fin d, ‖F x j‖ ^ 2)) 2 m ∧
        MemLp q 2 m := by
  classical
  dsimp only
  let m := volume.restrict {x : Vec d | euclideanNorm (x - z) < ρ}
  have hv := localSpatialEnergy_window_volume z ρ hρ
  have hfin := (ENNReal.toReal_pos_iff.mp hv).2.ne
  let : IsFiniteMeasure m := ⟨by simpa only [m, Measure.restrict_apply_univ]
    using (lt_top_iff_ne_top.mpr hfin)⟩
  have horbit (W : Lp ℂ 2 (reducedLaw Q)) :
      ∀ᵐ ω ∂reducedLaw Q, IntegrableOn (fun x => ‖W (translate x ω)‖ ^ 2)
        {x : Vec d | euclideanNorm (x - z) < ρ} :=
    ae_integrableOn_stationary_orbit (reducedLaw_stationary Q)
      ((Lp.stronglyMeasurable W).measurable.norm.pow_const 2)
      ((Lp.memLp W).integrable_norm_pow (by norm_num)) hfin
  obtain ⟨Λ, A, B, hΛ, _, _, _, hbound⟩ :=
    node_eq_u2E_reduced_u2D_bounds_of_deps D.ellipticity D.one_le_ellipticity
  have hGorbit := (ae_all_iff).mpr (fun j : Fin d => horbit (G j))
  filter_upwards [horbit U, horbit V, hGorbit, (hbound d D.dependenceRange Q).2.2,
    fluxId_reduced_regular D Q hQ] with ω hU hV hG hω hreg
  have htr : Measurable (fun x : Vec d => translate x ω) :=
    (Probability.continuous_translate.comp (continuous_id.prodMk continuous_const)).measurable
  have hmem (W : Lp ℂ 2 (reducedLaw Q))
      (hW : IntegrableOn (fun x => ‖W (translate x ω)‖ ^ 2)
        {x : Vec d | euclideanNorm (x - z) < ρ}) :
      MemLp (fun x => W (translate x ω)) 2 m :=
    (memLp_two_iff_integrable_sq_norm
      (((Lp.stronglyMeasurable W).measurable.comp htr).aestronglyMeasurable.restrict)).mpr
        hW.integrable
  have hUm := hmem U hU
  have hVm := hmem V hV
  have hGm := fun j => hmem (G j) (hG j)
  have hF : ∀ j : Fin d, MemLp (fun x => G j (translate x ω) -
      match ν with
      | .inr true => 2 * ζ * (unitVector (⟨0, by omega⟩ : Fin d) j : ℂ) * U (translate x ω)
      | _ => 0) 2 m := by
    intro j
    split
    · exact (hGm j).sub (hUm.const_mul _)
    · simpa only [sub_zero] using hGm j
  have haG : MemLp (fun x => ∑ k : Fin d,
      (ω.1 x k ⟨0, by omega⟩ : ℂ) * G k (translate x ω)) 2 m := by
    apply memLp_finsetSum _
    intro k _
    have ha : MemLp (fun x => (ω.1 x k ⟨0, by omega⟩ : ℂ)) ∞ m :=
      memLp_top_of_bound
        ((Complex.continuous_ofReal.comp
          (hreg.1 k ⟨0, by omega⟩).continuous).aestronglyMeasurable)
          Λ (Filter.Eventually.of_forall fun x => by
          simpa only [Complex.norm_real, Real.norm_eq_abs] using
            abs_apply_le_of_isElliptic (lt_of_lt_of_le zero_lt_one hΛ) hω.1 x k
              ⟨0, by omega⟩)
    exact ha.mul (hGm k)
  refine ⟨hUm, hVm, hGm, carverS_memLp_spatial_vector_energy m _ hF, ?_⟩
  split
  · simpa only [add_zero] using hVm.const_mul (2 : ℂ)
  · exact (hVm.const_mul (2 : ℂ)).add
      ((memLp_const (2 * c)).sub (haG.const_mul (2 * ζ)))

private theorem carverS_l2_mono {α 𝕜 𝕝 : Type*} [MeasurableSpace α]
    [RCLike 𝕜] [RCLike 𝕝] {m : Measure α} {f : α → 𝕜} {g : α → 𝕝}
    (hf : MemLp f 2 m) (hg : MemLp g 2 m)
    (h : ∀ᵐ x ∂m, ‖f x‖ ≤ ‖g x‖) :
    Calculus.S1.l2Size m f ≤ Calculus.S1.l2Size m g := by
  apply Real.sqrt_le_sqrt
  exact integral_mono_ae (hf.integrable_norm_pow (by norm_num))
    (hg.integrable_norm_pow (by norm_num))
    (h.mono fun x hx => (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hx)

private theorem carverS_l2_const_mul {α 𝕜 : Type*} [MeasurableSpace α] [RCLike 𝕜]
    (m : Measure α) (c : 𝕜) (f : α → 𝕜) :
    Calculus.S1.l2Size m (fun x => c * f x) = ‖c‖ * Calculus.S1.l2Size m f := by
  unfold Calculus.S1.l2Size
  simp only [norm_mul, mul_pow, integral_const_mul]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

private theorem carverS_l2_const {α 𝕜 : Type*} [MeasurableSpace α] [RCLike 𝕜]
    (m : Measure α) (c : 𝕜) :
    Calculus.S1.l2Size m (fun _ : α => c) = ‖c‖ * Real.sqrt (m.real Set.univ) := by
  unfold Calculus.S1.l2Size
  rw [integral_const, smul_eq_mul, Real.sqrt_mul measureReal_nonneg,
    Real.sqrt_sq (norm_nonneg _), mul_comm]

private theorem carverS_l2_real_add_norm {α : Type*} [MeasurableSpace α]
    (m : Measure α) (f : α → ℝ) (u : α → ℂ) (hf : MemLp f 2 m)
    (hu : MemLp u 2 m) (b : ℝ) (hb : 0 ≤ b) :
    Calculus.S1.l2Size m (fun x => f x + b * ‖u x‖) ≤
      Calculus.S1.l2Size m f + b * Calculus.S1.l2Size m u := by
  have hh := Calculus.S1.l2Size_add_le hf (hu.norm.const_mul b)
  simpa only [Pi.add_def, carverS_l2_const_mul, Real.norm_eq_abs, abs_of_nonneg hb,
    Calculus.S1.l2Size_norm] using hh

private theorem carverS_l2_time_divergence {α : Type*} [MeasurableSpace α]
    (m : Measure α) [IsFiniteMeasure m] (v f : α → ℂ)
    (hv : MemLp v 2 m) (hf : MemLp f 2 m) (ζ c : ℂ) :
    Calculus.S1.l2Size m (fun x => 2 * v x + (2 * c - 2 * ζ * f x)) ≤
      2 * Calculus.S1.l2Size m v + 2 * ‖c‖ * Real.sqrt (m.real Set.univ) +
        2 * ‖ζ‖ * Calculus.S1.l2Size m f := by
  have hv2 : MemLp (fun x => (2 : ℂ) * v x) 2 m := hv.const_mul (2 : ℂ)
  have hc2 : MemLp (fun _ : α => (2 : ℂ) * c) 2 m := memLp_const ((2 : ℂ) * c)
  have hf2 : MemLp (fun x => ((2 : ℂ) * ζ) * f x) 2 m := hf.const_mul ((2 : ℂ) * ζ)
  have hsub := Calculus.S1.l2Size_sub_le hc2 hf2
  have hadd := Calculus.S1.l2Size_add_le hv2 (hc2.sub hf2)
  simp only [Pi.add_def, Pi.sub_def] at hadd hsub
  calc
    _ ≤ Calculus.S1.l2Size m (fun x => (2 : ℂ) * v x) +
        Calculus.S1.l2Size m (fun x => 2 * c - 2 * ζ * f x) :=
      hadd
    _ ≤ Calculus.S1.l2Size m (fun x => (2 : ℂ) * v x) +
        (Calculus.S1.l2Size m (fun _ => (2 : ℂ) * c) +
          Calculus.S1.l2Size m (fun x => (2 * ζ) * f x)) :=
      add_le_add (le_refl (Calculus.S1.l2Size m (fun x => (2 : ℂ) * v x))) hsub
    _ = _ := by
      rw [carverS_l2_const_mul, carverS_l2_const, carverS_l2_const_mul]
      simp only [norm_mul, Complex.norm_two]
      ring

private theorem carverS_shifted_gradient_energy_le {d : ℕ} (hd : 2 ≤ d)
    (u : ℂ) (g : Fin d → ℂ) (ν : EndpointIndex d) (ζ : ℂ) :
    Real.sqrt (∑ j : Fin d, ‖g j -
      (match ν with
      | .inr true => 2 * ζ * (unitVector (⟨0, by omega⟩ : Fin d) j : ℂ) * u
      | _ => 0)‖ ^ 2) ≤
      (d : ℝ) * (Real.sqrt (∑ j : Fin d, ‖g j‖ ^ 2) + 2 * ‖ζ‖ * ‖u‖) := by
  classical
  let E := Real.sqrt (∑ j : Fin d, ‖g j‖ ^ 2)
  let F := fun j => g j - match ν with
    | .inr true => 2 * ζ * (unitVector (⟨0, by omega⟩ : Fin d) j : ℂ) * u
    | _ => 0
  have hpoint (j : Fin d) : ‖F j‖ ≤ E + 2 * ‖ζ‖ * ‖u‖ := by
    have hunit : ‖(unitVector (⟨0, by omega⟩ : Fin d) j : ℂ)‖ ≤ 1 := by
      by_cases h : (⟨0, by omega⟩ : Fin d) = j <;> simp [unitVector, h]
    apply (norm_sub_le _ _).trans
    apply add_le_add (carverS_norm_component_le_energy g j)
    split
    · calc
        _ = 2 * ‖ζ‖ * ‖(unitVector (⟨0, by omega⟩ : Fin d) j : ℂ)‖ * ‖u‖ := by
          simp only [norm_mul, Complex.norm_two]
        _ ≤ 2 * ‖ζ‖ * 1 * ‖u‖ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hunit (by positivity)) (norm_nonneg _)
        _ = _ := by ring
    · simp only [norm_zero]; positivity
  have hA : 0 ≤ E + 2 * ‖ζ‖ * ‖u‖ := by dsimp [E]; positivity
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hd2 : (d : ℝ) ≤ (d : ℝ) ^ 2 := by nlinarith
  change Real.sqrt (∑ j : Fin d, ‖F j‖ ^ 2) ≤ (d : ℝ) * (E + 2 * ‖ζ‖ * ‖u‖)
  apply Real.sqrt_le_iff.mpr ⟨mul_nonneg (Nat.cast_nonneg _) hA, ?_⟩
  calc
    _ ≤ ∑ _j : Fin d, (E + 2 * ‖ζ‖ * ‖u‖) ^ 2 :=
      Finset.sum_le_sum fun j _ => (sq_le_sq₀ (norm_nonneg _) hA).mpr (hpoint j)
    _ = (d : ℝ) * (E + 2 * ‖ζ‖ * ‖u‖) ^ 2 := by simp
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_right hd2 (sq_nonneg (E + 2 * ‖ζ‖ * ‖u‖))
      nlinarith only [hh]

/-- Quantitative L² control of the literal shifted gradient and divergence.
The coefficient column is the actual column appearing in the endpoint identity. -/
theorem carverS_flux_block_endpoint_fields_l2 {d : ℕ} (hd : 2 ≤ d)
    (m : Measure (Vec d)) [IsFiniteMeasure m]
    (u v : Vec d → ℂ) (g : Vec d → Fin d → ℂ) (a : Vec d → Fin d → ℝ)
    (hu : MemLp u 2 m) (hv : MemLp v 2 m)
    (hg : ∀ j, MemLp (fun x => g x j) 2 m)
    (ha : ∀ j, AEStronglyMeasurable (fun x => (a x j : ℂ)) m)
    (M : ℝ) (hM : 0 ≤ M) (hab : ∀ᵐ x ∂m, ∀ j, |a x j| ≤ M)
    (ν : EndpointIndex d) (ζ c : ℂ) :
    let E := fun x => Real.sqrt (∑ j : Fin d, ‖g x j‖ ^ 2)
    let F := fun (x : Vec d) (j : Fin d) => g x j -
      match ν with
      | .inr true => 2 * ζ * (unitVector (⟨0, by omega⟩ : Fin d) j : ℂ) * u x
      | _ => 0
    let q := fun x => 2 * v x +
      match ν with
      | .inr true => 0
      | _ => 2 * c - 2 * ζ * (∑ j : Fin d, (a x j : ℂ) * g x j)
    Calculus.S1.l2Size m (fun x => Real.sqrt (∑ j : Fin d, ‖F x j‖ ^ 2)) ≤
      (d : ℝ) * (Calculus.S1.l2Size m E + 2 * ‖ζ‖ * Calculus.S1.l2Size m u) ∧
    Calculus.S1.l2Size m q ≤ 2 * Calculus.S1.l2Size m v +
      2 * ‖c‖ * Real.sqrt (m.real Set.univ) +
      2 * ‖ζ‖ * ((d : ℝ) * M * Calculus.S1.l2Size m E) := by
  classical
  dsimp only
  let E := fun x => Real.sqrt (∑ j : Fin d, ‖g x j‖ ^ 2)
  let F := fun (x : Vec d) (j : Fin d) => g x j -
    match ν with
    | .inr true => 2 * ζ * (unitVector (⟨0, by omega⟩ : Fin d) j : ℂ) * u x
    | _ => 0
  have hE : MemLp E 2 m := carverS_memLp_spatial_vector_energy m (fun j x => g x j) hg
  have hF : ∀ j : Fin d, MemLp (fun x => F x j) 2 m := by
    intro j
    dsimp only [F]
    split
    · exact (hg j).sub (hu.const_mul _)
    · simpa only [sub_zero] using hg j
  have hFE := carverS_memLp_spatial_vector_energy m (fun j x => F x j) hF
  have hpointE (x : Vec d) : Real.sqrt (∑ j : Fin d, ‖F x j‖ ^ 2) ≤
      (d : ℝ) * (E x + 2 * ‖ζ‖ * ‖u x‖) :=
    carverS_shifted_gradient_energy_le hd (u x) (g x) ν ζ
  have hag : MemLp (fun x => ∑ j : Fin d, (a x j : ℂ) * g x j) 2 m := by
    apply memLp_finsetSum _
    intro j _
    have hj : MemLp (fun x => (a x j : ℂ)) ∞ m := memLp_top_of_bound (ha j) M
      (hab.mono fun x hx => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hx j)
    exact hj.mul (hg j)
  have hagpoint : ∀ᵐ x ∂m, ‖∑ j : Fin d, (a x j : ℂ) * g x j‖ ≤ (d : ℝ) * M * E x :=
    hab.mono fun x hx => carverS_norm_sum_mul_le _ _ hM
      (fun j => by simpa only [Complex.norm_real, Real.norm_eq_abs] using hx j)
      (carverS_norm_component_le_energy (g x))
  have hagL2 : Calculus.S1.l2Size m (fun x => ∑ j : Fin d, (a x j : ℂ) * g x j) ≤
      (d : ℝ) * M * Calculus.S1.l2Size m E := by
    calc
      _ ≤ Calculus.S1.l2Size m (fun x => ((d : ℝ) * M) * E x) :=
        carverS_l2_mono hag (hE.const_mul _) (hagpoint.mono fun x hx => by
          have hn : 0 ≤ (d : ℝ) * M * E x :=
            mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hM) (Real.sqrt_nonneg _)
          rw [Real.norm_eq_abs, abs_of_nonneg hn]
          exact hx)
      _ = _ := by rw [carverS_l2_const_mul, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hM)]
  constructor
  · change Calculus.S1.l2Size m (fun x => Real.sqrt (∑ j : Fin d, ‖F x j‖ ^ 2)) ≤ _
    calc
      _ ≤ Calculus.S1.l2Size m (fun x => (d : ℝ) * (E x + 2 * ‖ζ‖ * ‖u x‖)) :=
        carverS_l2_mono hFE ((hE.add (hu.norm.const_mul _)).const_mul _)
          (Filter.Eventually.of_forall fun x => by
            simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
              abs_of_nonneg (by dsimp [E]; positivity :
                0 ≤ (d : ℝ) * (E x + 2 * ‖ζ‖ * ‖u x‖))] using hpointE x)
      _ ≤ _ := by
        rw [carverS_l2_const_mul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        exact carverS_l2_real_add_norm m E u hE hu (2 * ‖ζ‖) (by positivity)
  · split
    · simp only [add_zero, carverS_l2_const_mul, Complex.norm_two]
      have hconst : 0 ≤ 2 * ‖c‖ * Real.sqrt (m.real Set.univ) := by positivity
      have hgrad : 0 ≤ 2 * ‖ζ‖ * ((d : ℝ) * M * Calculus.S1.l2Size m E) :=
        mul_nonneg (by positivity)
          (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hM) (Calculus.S1.l2Size_nonneg _))
      linarith
    · exact (carverS_l2_time_divergence m v _ hv hag ζ c).trans
        (add_le_add (le_refl (2 * Calculus.S1.l2Size m v +
          2 * ‖c‖ * Real.sqrt (m.real Set.univ)))
          (mul_le_mul_of_nonneg_left hagL2 (show 0 ≤ 2 * ‖ζ‖ by positivity)))

/-- Quantitative endpoint bounds on the original spatial window. The value,
time derivative and centering constant are the literal endpoint quantities;
the coefficient constant is chosen before the environment law. -/
theorem carverS_flux_block_actual_endpoint_fields_l2 (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) :
    ∃ M : ℝ, 1 ≤ M ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
      (ζ : ℂ)
      (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
      (ν : EndpointIndex d) (t : ℝ≥0) (ρ : ℝ) (hρ : 0 < ρ) (z : Vec d)
      (G : Fin d → Lp ℂ 2 (reducedLaw Q)),
      let U := indexedEndpoint hd Q ν ζ P Pdag β a μ t
      let V := deriv (fun r : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ r.toNNReal)
        (t : ℝ)
      let c := ζ * ∫ ω, ∑ k : Fin d,
        a k ⟨0, by omega⟩ ω * G k ω ∂reducedLaw Q
      let m := volume.restrict {x : Vec d | euclideanNorm (x - z) < ρ}
      ∀ᵐ ω ∂reducedLaw Q,
        let u := fun x : Vec d => U (translate x ω)
        let v := fun x : Vec d => V (translate x ω)
        let g := fun (x : Vec d) (j : Fin d) => G j (translate x ω)
        let E := fun x => Real.sqrt (∑ j : Fin d, ‖g x j‖ ^ 2)
        let F := fun (x : Vec d) (j : Fin d) => g x j -
          match ν with
          | .inr true => 2 * ζ * (unitVector (⟨0, by omega⟩ : Fin d) j : ℂ) * u x
          | _ => 0
        let q := fun x : Vec d => 2 * v x +
          match ν with
          | .inr true => 0
          | _ => 2 * c - 2 * ζ * (∑ k : Fin d,
              (ω.1 x k ⟨0, by omega⟩ : ℂ) * g x k)
        Calculus.S1.l2Size m (fun x => Real.sqrt (∑ j : Fin d, ‖F x j‖ ^ 2)) ≤
          (d : ℝ) * (Calculus.S1.l2Size m E + 2 * ‖ζ‖ * Calculus.S1.l2Size m u) ∧
        Calculus.S1.l2Size m q ≤ 2 * Calculus.S1.l2Size m v +
          2 * ‖c‖ * Real.sqrt (m.real Set.univ) +
          2 * ‖ζ‖ * ((d : ℝ) * M * Calculus.S1.l2Size m E) := by
  classical
  obtain ⟨M, A, B, hM, _, _, _, hbound⟩ :=
    node_eq_u2E_reduced_u2D_bounds_of_deps D.ellipticity D.one_le_ellipticity
  refine ⟨M, hM, ?_⟩
  intro Q hQ β a μ ζ P Pdag ν t ρ hρ z G
  dsimp only
  let U := indexedEndpoint hd Q ν ζ P Pdag β a μ t
  let V := deriv (fun r : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ r.toNNReal)
    (t : ℝ)
  let c := ζ * ∫ ω, ∑ k : Fin d,
    a k ⟨0, by omega⟩ ω * G k ω ∂reducedLaw Q
  let m := volume.restrict {x : Vec d | euclideanNorm (x - z) < ρ}
  have hvol := localSpatialEnergy_window_volume z ρ hρ
  let : IsFiniteMeasure m := ⟨by
    simpa only [m, Measure.restrict_apply_univ] using
      (lt_top_iff_ne_top.mpr (ENNReal.toReal_pos_iff.mp hvol).2.ne)⟩
  filter_upwards [carverS_flux_block_endpoint_fields_memLp hd D Q hQ ρ hρ z U V G ν ζ c,
    (hbound d D.dependenceRange Q).2.2, fluxId_reduced_regular D Q hQ]
    with ω hfields hω hreg
  apply carverS_flux_block_endpoint_fields_l2 hd m
    (fun x => U (translate x ω)) (fun x => V (translate x ω))
    (fun x j => G j (translate x ω))
    (fun x k => ω.1 x k ⟨0, by omega⟩)
    hfields.1 hfields.2.1 hfields.2.2.1
    (fun k => (Complex.continuous_ofReal.comp
      (hreg.1 k ⟨0, by omega⟩).continuous).aestronglyMeasurable)
    M (zero_le_one.trans hM) _ ν ζ c
  exact Filter.Eventually.of_forall fun x k =>
    abs_apply_le_of_isElliptic (zero_lt_one.trans_le hM) hω.1 x k ⟨0, by omega⟩

/-- The actual centering integral is controlled by the original coefficient
observations and the global L² norms of the same gradient representatives. -/
theorem carverS_flux_block_centering_integral_bound (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) :
    ∃ M : ℝ, 1 ≤ M ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)),
      IsReducedCoefficientObservation Q a →
      ∀ (G : Fin d → Lp ℂ 2 (reducedLaw Q)) (ζ : ℂ),
      ‖ζ * ∫ ω, ∑ k : Fin d,
        a k ⟨0, by omega⟩ ω * G k ω ∂reducedLaw Q‖ ≤
        ‖ζ‖ * M * ∑ k : Fin d, ‖G k‖ := by
  obtain ⟨M, A, B, hM, _, _, _, hbound⟩ :=
    node_eq_u2E_reduced_u2D_bounds_of_deps D.ellipticity D.one_le_ellipticity
  refine ⟨M, hM, ?_⟩
  intro Q a ha G ζ
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hcoeff (k : Fin d) : Calculus.S1.l2Size (reducedLaw Q)
      (a k ⟨0, by omega⟩ : FieldPair d → ℂ) ≤ M := by
    calc
      _ ≤ Calculus.S1.l2Size (reducedLaw Q) (fun _ : FieldPair d => (M : ℂ)) := by
        apply carverS_l2_mono (Lp.memLp _) (memLp_const (M : ℂ))
        filter_upwards [(hbound d D.dependenceRange Q).2.2, ha k ⟨0, by omega⟩]
          with ω hω haω
        rw [haω, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg hM0]
        exact abs_apply_le_of_isElliptic (zero_lt_one.trans_le hM) hω.1 0 k
          ⟨0, by omega⟩
      _ = M := by
        rw [carverS_l2_const, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hM0]
        simp
  have hpair (k : Fin d) :
      ‖∫ ω, a k ⟨0, by omega⟩ ω * G k ω ∂reducedLaw Q‖ ≤ M * ‖G k‖ := by
    have hh := Calculus.S1.norm_integral_mul_le_l2Size
      (Lp.memLp (a k ⟨0, by omega⟩)) (Lp.memLp (G k))
    rw [Calculus.S1.l2Size_lp (G k)] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (hcoeff k) (norm_nonneg _))
  have hsum :
      ‖∫ ω, ∑ k : Fin d, a k ⟨0, by omega⟩ ω * G k ω ∂reducedLaw Q‖ ≤
        M * ∑ k : Fin d, ‖G k‖ := by
    rw [integral_finsetSum Finset.univ (fun k _ =>
      (Lp.memLp (a k ⟨0, by omega⟩)).integrable_mul (Lp.memLp (G k)))]
    exact (norm_sum_le _ _).trans ((Finset.sum_le_sum fun k _ => hpair k).trans_eq
      (Finset.mul_sum Finset.univ (fun k : Fin d => ‖G k‖) M).symm)
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left hsum (norm_nonneg ζ)).trans_eq (by ring)

private theorem carverS_stationary_ball_average_integral {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (f : FieldPair d → ℝ)
    (hfm : Measurable f) (hfi : Integrable f (reducedLaw Q))
    (ρ : ℝ) (hρ : 0 < ρ) (z : Vec d) :
    (∫ ω, (⨍ x in {x : Vec d | euclideanNorm (x - z) < ρ},
      f (translate x ω)) ∂reducedLaw Q) = ∫ ω, f ω ∂reducedLaw Q := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let B := {x : Vec d | euclideanNorm (x - z) < ρ}
  have hvol : 0 < volume.real B := localSpatialEnergy_window_volume z ρ hρ
  have hfin : volume B ≠ ⊤ := (ENNReal.toReal_pos_iff.mp hvol).2.ne
  let : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr hfin
  have hFm : Measurable (fun p : FieldPair d × Vec d => f (translate p.2 p.1)) :=
    hfm.comp (Probability.continuous_translate.measurable.comp
      (measurable_snd.prodMk measurable_fst))
  have hFint : Integrable (fun p : FieldPair d × Vec d => f (translate p.2 p.1))
      ((reducedLaw Q).prod (volume.restrict B)) := by
    rw [integrable_prod_iff' hFm.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun x => ?_, ?_⟩
    · have h : Integrable f (Measure.map (translate x) (reducedLaw Q)) := by
        rw [reducedLaw_stationary Q x]
        exact hfi
      exact h.comp_measurable (Probability.measurable_translate x)
    · apply (integrable_const (∫ ω, ‖f ω‖ ∂reducedLaw Q)).congr
      exact Filter.Eventually.of_forall fun x =>
        (Probability.integral_translate (reducedLaw Q) (reducedLaw_stationary Q) x
          (fun ω => ‖f ω‖) hfm.norm).symm
  change (∫ ω, (⨍ x in B, f (translate x ω)) ∂reducedLaw Q) = _
  simp only [average_eq, measureReal_restrict_apply_univ, smul_eq_mul]
  rw [integral_const_mul, integral_integral_swap hFint]
  simp_rw [Probability.integral_translate (reducedLaw Q) (reducedLaw_stationary Q) _ f hfm]
  rw [integral_const, smul_eq_mul, measureReal_restrict_apply_univ,
    ← mul_assoc, inv_mul_cancel₀ hvol.ne', one_mul]

/-- The global L² norm of every original gradient component is controlled
by the actual local energy on any positive-radius window, by stationarity. -/
theorem carverS_flux_block_global_gradient_l2_le_energy {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (t : ℝ≥0)
    (ρ : ℝ) (hρ : 0 < ρ) (z : Vec d)
    (G : Fin d → Lp ℂ 2 (reducedLaw Q)) (V : Lp ℂ 2 (reducedLaw Q))
    (j : Fin d) :
    ‖G j‖ ≤ Calculus.S1.l2Size (reducedLaw Q)
      (localSpatialEnergy Q t ρ hρ z G V) := by
  let H := fun ω : FieldPair d =>
    (∑ k : Fin d, ‖G k ω‖ ^ 2) + (t : ℝ) * ‖V ω‖ ^ 2
  have hHm : Measurable H :=
    (Finset.measurable_sum _ fun k _ =>
      (Lp.stronglyMeasurable (G k)).measurable.norm.pow_const 2).add
      (measurable_const.mul ((Lp.stronglyMeasurable V).measurable.norm.pow_const 2))
  have hHi : Integrable H (reducedLaw Q) :=
    (integrable_finsetSum _ fun k _ =>
      (Lp.memLp (G k)).integrable_norm_pow (by norm_num)).add
      (((Lp.memLp V).integrable_norm_pow (by norm_num)).const_mul (t : ℝ))
  rw [← Calculus.S1.l2Size_lp (G j)]
  unfold Calculus.S1.l2Size
  apply Real.sqrt_le_sqrt
  calc
    _ ≤ ∫ ω, H ω ∂reducedLaw Q :=
      integral_mono ((Lp.memLp (G j)).integrable_norm_pow (by norm_num)) hHi
        (fun ω => (Finset.single_le_sum
          (fun k _ => sq_nonneg ‖G k ω‖) (Finset.mem_univ j)).trans
          (le_add_of_nonneg_right (mul_nonneg t.property (sq_nonneg ‖V ω‖))))
    _ = ∫ ω, ‖localSpatialEnergy Q t ρ hρ z G V ω‖ ^ 2 ∂reducedLaw Q := by
      symm
      simp only [Real.norm_eq_abs, sq_abs, localSpatialEnergy_sq]
      exact carverS_stationary_ball_average_integral Q H hHm hHi ρ hρ z

/-- The original centering constant is controlled by any available local-time
energy moment at exponent at least two, retaining the same gradient. -/
theorem carverS_flux_block_centering_integral_le_energy (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) :
    ∃ M : ℝ, 1 ≤ M ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)),
      IsReducedCoefficientObservation Q a →
      ∀ (G : Fin d → Lp ℂ 2 (reducedLaw Q)) (ζ : ℂ)
        (t : ℝ≥0) (ρ : ℝ) (hρ : 0 < ρ) (z : Vec d)
        (V : Lp ℂ 2 (reducedLaw Q)) (p : ℝ≥0∞), 2 ≤ p →
      MemLp (localSpatialEnergy Q t ρ hρ z G V) p (reducedLaw Q) →
      ‖ζ * ∫ ω, ∑ k : Fin d,
        a k ⟨0, by omega⟩ ω * G k ω ∂reducedLaw Q‖ ≤
        ‖ζ‖ * ((d : ℝ) * M) *
          (eLpNorm (localSpatialEnergy Q t ρ hρ z G V) p (reducedLaw Q)).toReal := by
  obtain ⟨M, hM, hcenter⟩ := carverS_flux_block_centering_integral_bound d hd D
  refine ⟨M, hM, ?_⟩
  intro Q a ha G ζ t ρ hρ z V p hp hE
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hLp : Calculus.S1.l2Size (reducedLaw Q)
      (localSpatialEnergy Q t ρ hρ z G V) ≤
      (eLpNorm (localSpatialEnergy Q t ρ hρ z G V) p (reducedLaw Q)).toReal := by
    rw [Calculus.S1.l2Size_eq_norm_toLp (hE.mono_exponent hp), Lp.norm_toLp]
    exact ENNReal.toReal_mono hE.eLpNorm_ne_top (eLpNorm_le_eLpNorm_of_exponent_le hp)
  have hsum : (∑ k : Fin d, ‖G k‖) ≤ (d : ℝ) *
      (eLpNorm (localSpatialEnergy Q t ρ hρ z G V) p (reducedLaw Q)).toReal := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun k _ =>
      (carverS_flux_block_global_gradient_l2_le_energy Q t ρ hρ z G V k).trans hLp)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hh
  exact (hcenter Q a ha G ζ).trans
    ((mul_le_mul_of_nonneg_left hsum
      (mul_nonneg (norm_nonneg ζ) (zero_le_one.trans hM))).trans_eq (by ring))

private theorem carverS_cutoff_iterated_derivative {d k : ℕ}
    (f : Vec d → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (dirs : Fin k → Fin d) (x z y : Vec d) (j : Fin d) :
    fderiv ℝ (fun v => (χ (v - z) : ℂ) *
      iteratedFDeriv ℝ k f (x - v) (fun l => unitVector (dirs l))) y (unitVector j) =
      (fderiv ℝ χ (y - z) (unitVector j) : ℂ) *
        iteratedFDeriv ℝ k f (x - y) (fun l => unitVector (dirs l)) -
      (χ (y - z) : ℂ) * iteratedFDeriv ℝ (k + 1) f (x - y)
        (fun l => unitVector ((Fin.cons j dirs : Fin (k + 1) → Fin d) l)) := by
  have hf' := hf.differentiable_iteratedFDeriv (m := k) (by
    exact WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top _)) (x - y)
  have heval := hf'.continuousMultilinear_apply_const (fun l => unitVector (dirs l))
  have hc := Complex.ofRealCLM.hasFDerivAt.comp y
    (((hχ.differentiable (by simp)) (y - z)).hasFDerivAt.comp y
      (hasFDerivAt_sub_const z))
  have hk := heval.hasFDerivAt.comp y ((hasFDerivAt_id y).const_sub x)
  have hm := congrArg (fun L : Vec d →L[ℝ] ℂ => L (unitVector j)) (hc.mul hk).fderiv
  simp only [Function.comp_def, add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, neg_apply, ContinuousLinearMap.id_apply,
    Complex.ofRealCLM_apply, smul_eq_mul, map_neg] at hm
  change fderiv ℝ (fun v => (χ (v - z) : ℂ) *
      iteratedFDeriv ℝ k f (x - v) (fun l => unitVector (dirs l))) y (unitVector j) =
      (χ (y - z) : ℂ) *
        -(fderiv ℝ (fun v => iteratedFDeriv ℝ k f v (fun l => unitVector (dirs l)))
          (x - y) (unitVector j)) +
      iteratedFDeriv ℝ k f (x - y) (fun l => unitVector (dirs l)) *
        (fderiv ℝ χ (y - z) (unitVector j) : ℂ) at hm
  have htail : Fin.tail (fun l => unitVector ((Fin.cons j dirs : Fin (k + 1) → Fin d) l)) =
      (fun l => unitVector (dirs l)) := by
    funext l
    exact congrArg (unitVector : Fin d → Vec d)
      (Fin.cons_succ (α := fun _ : Fin (k + 1) => Fin d) j dirs l)
  have hn : iteratedFDeriv ℝ (k + 1) f (x - y)
      (fun l => unitVector ((Fin.cons j dirs : Fin (k + 1) → Fin d) l)) =
      fderiv ℝ (fun v => iteratedFDeriv ℝ k f v (fun l => unitVector (dirs l)))
        (x - y) (unitVector j) := by
    simpa only [htail, Fin.cons_zero] using
      hf'.iteratedFDeriv_succ_apply_left'
        (m := fun l => unitVector ((Fin.cons j dirs : Fin (k + 1) → Fin d) l))
  rw [hn]
  rw [hm]
  ring

/-- Differentiating the actual cutoff coordinate kernel is bounded by the same
spatial Gaussian supremum, with constants chosen before the law and scales. -/
theorem carverS_flux_block_cutoff_kernel_derivative_bound (d : ℕ) (D : StructuralData d) :
    ∃ Cenv : ℝ, ∃ Cder : ℕ → ℝ, 1 ≤ Cenv ∧ (∀ k, 1 ≤ Cder k) ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (i : Fin d)
      (r : ℝ) (_hr : 0 < r) (s : ℝ) (hs : 0 < s) (χ : Vec d → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
      let R := 2 * Real.sqrt (d : ℝ) + 2
      Function.support χ ⊆ {y : Vec d | euclideanNorm y ≤ R * r} →
      (∀ y, |χ y| ≤ 1) →
      (∀ y, Real.sqrt (∑ j : Fin d, (fderiv ℝ χ y (unitVector j)) ^ 2) ≤ R / r) →
      ∀ (k : ℕ) (dirs : Fin k → Fin d) (x z y : Vec d),
      euclideanNorm (y - z) ≤ R * r →
      let ψ : Vec d → ℂ := fun v => (χ (v - z) : ℂ) *
        iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i s hs 0) (x - v)
          (fun j => unitVector (dirs j))
      let W := sSup ((fun v : Vec d => s ^ (-(d : ℝ) / 2) *
        Real.exp (-euclideanNorm (x - v) ^ 2 / (Cenv * s))) ''
          {v : Vec d | euclideanNorm (v - z) ≤ R * r})
      ∀ j : Fin d, ‖fderiv ℝ ψ y (unitVector j)‖ ≤
        (Cder k * (R / r) * s ^ (-(k : ℝ) / 2) +
          Cder (k + 1) * s ^ (-((k + 1 : ℕ) : ℝ) / 2)) * W := by
  obtain ⟨Cenv, Cder, hCenv, hCder, hkernel⟩ :=
    carverS_flux_block_gaussian_envelope d D
  refine ⟨Cenv, Cder, hCenv, hCder, ?_⟩
  intro Q i r hr s hs χ hχ _hcompact R _hsupp hχabs hχgrad k dirs x z y hy ψ W j
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hD (n : ℕ) : 0 ≤ Cder n := (zero_le_one.trans (hCder n))
  have hsup := carverS_flux_block_gaussian_spatial_sup s hs Cenv x z (R * r)
    (mul_nonneg hR hr.le)
  have hk : ‖iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i s hs 0) (x - y)
      (fun l => unitVector (dirs l))‖ ≤ Cder k * s ^ (-(k : ℝ) / 2) * W :=
    (hkernel Q i s hs k dirs (x - y)).trans
      (mul_le_mul_of_nonneg_left (hsup.2.2 y hy)
        (mul_nonneg (hD k) (Real.rpow_nonneg hs.le _)))
  have hk' : ‖iteratedFDeriv ℝ (k + 1) (homogenizedGaussianKernel Q i s hs 0) (x - y)
      (fun l => unitVector ((Fin.cons j dirs : Fin (k + 1) → Fin d) l))‖ ≤
      Cder (k + 1) * s ^ (-((k + 1 : ℕ) : ℝ) / 2) * W :=
    (hkernel Q i s hs (k + 1) (Fin.cons j dirs) (x - y)).trans
      (mul_le_mul_of_nonneg_left (hsup.2.2 y hy)
        (mul_nonneg (hD (k + 1)) (Real.rpow_nonneg hs.le _)))
  have hχj : |fderiv ℝ χ (y - z) (unitVector j)| ≤ R / r :=
    (Real.abs_le_sqrt (Finset.single_le_sum
      (fun l _ => sq_nonneg (fderiv ℝ χ (y - z) (unitVector l)))
        (Finset.mem_univ j))).trans (hχgrad (y - z))
  change ‖fderiv ℝ (fun v => (χ (v - z) : ℂ) *
    iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i s hs 0) (x - v)
      (fun l => unitVector (dirs l))) y (unitVector j)‖ ≤ _
  rw [carverS_cutoff_iterated_derivative _
    (contDiff_homogenizedGaussianKernel_complexForce Q i s hs 0) χ hχ dirs x z y j]
  calc
    _ ≤ |fderiv ℝ χ (y - z) (unitVector j)| *
          ‖iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i s hs 0) (x - y)
            (fun l => unitVector (dirs l))‖ + |χ (y - z)| *
          ‖iteratedFDeriv ℝ (k + 1) (homogenizedGaussianKernel Q i s hs 0) (x - y)
            (fun l => unitVector ((Fin.cons j dirs : Fin (k + 1) → Fin d) l))‖ := by
      simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs] using
        norm_sub_le
          ((fderiv ℝ χ (y - z) (unitVector j) : ℂ) *
            iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i s hs 0) (x - y)
              (fun l => unitVector (dirs l)))
          ((χ (y - z) : ℂ) *
            iteratedFDeriv ℝ (k + 1) (homogenizedGaussianKernel Q i s hs 0) (x - y)
              (fun l => unitVector ((Fin.cons j dirs : Fin (k + 1) → Fin d) l)))
    _ ≤ (R / r) * (Cder k * s ^ (-(k : ℝ) / 2) * W) +
        1 * (Cder (k + 1) * s ^ (-((k + 1 : ℕ) : ℝ) / 2) * W) :=
      add_le_add (mul_le_mul hχj hk (norm_nonneg _) (div_nonneg hR hr.le))
        (mul_le_mul (hχabs (y - z)) hk' (norm_nonneg _) zero_le_one)
    _ = _ := by ring

private theorem carverS_two_corrector_sizes_bound
    (X Y H A B M Z n q f g : ℝ)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hM : 0 ≤ M) (hZ : 0 ≤ Z) (hn : 0 ≤ n)
    (hq : 0 ≤ q) (hf : 0 ≤ f) (hg : 0 ≤ g) (hsize : X + Y ≤ H) :
    X * (A * q + n ^ 2 * M * B * f) +
      Y * (n ^ 2 * B * f + 2 * Z * n * A * g) ≤
      H * (A * q + n ^ 2 * (M + 1) * B * f + 2 * Z * n * A * g) := by
  let W := A * q + n ^ 2 * (M + 1) * B * f + 2 * Z * n * A * g
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hfirst : A * q + n ^ 2 * M * B * f ≤ W := by
    dsimp only [W]
    nlinarith only [mul_nonneg (mul_nonneg (sq_nonneg n) hB) hf,
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        hZ) hn) hA) hg]
  have hsecond : n ^ 2 * B * f + 2 * Z * n * A * g ≤ W := by
    dsimp only [W]
    nlinarith only [mul_nonneg hA hq,
      mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg n) hM) hB) hf]
  calc
    _ ≤ X * W + Y * W := add_le_add
      (mul_le_mul_of_nonneg_left hfirst hX) (mul_le_mul_of_nonneg_left hsecond hY)
    _ = (X + Y) * W := (add_mul _ _ _).symm
    _ ≤ H * W := mul_le_mul_of_nonneg_right hsize hW

/-- On the original corrector oscillation window, the literal endpoint identity
is bounded by the same local energy, endpoint value and centering integral.
The last identity term retains its endpoint match, and the constant precedes
the environment law and all endpoint data. -/
theorem carverS_flux_block_actual_identity_oscillation_bound (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) :
    ∃ M : ℝ, 1 ≤ M ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
      (ζ : ℂ)
      (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
      (ν : EndpointIndex d) (t : ℝ≥0), 0 < (t : ℝ) →
    ∀ (ρ : ℝ) (hρ : 0 < ρ) (z : Vec d)
      (G : Fin d → Lp ℂ 2 (reducedLaw Q)),
      let U := indexedEndpoint hd Q ν ζ P Pdag β a μ t
      let V := deriv (fun r : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ r.toNNReal)
        (t : ℝ)
      let c := ζ * ∫ ω, ∑ k : Fin d,
        a k ⟨0, by omega⟩ ω * G k ω ∂reducedLaw Q
      let E := {x : Vec d | euclideanNorm (x - z) < ρ}
      ∀ᵐ ω ∂reducedLaw Q,
        let u := fun x : Vec d => U (translate x ω)
        let g := fun (x : Vec d) (j : Fin d) => G j (translate x ω)
        let F := fun (x : Vec d) (j : Fin d) => g x j -
          match (generalizing := false) ν with
          | .inr true => 2 * ζ * (unitVector (⟨0, by omega⟩ : Fin d) j : ℂ) * u x
          | _ => 0
        let q := fun x : Vec d => 2 * V (translate x ω) +
          match (generalizing := false) ν with
          | .inr true => 0
          | _ => 2 * c - 2 * ζ * (∑ k : Fin d,
              (ω.1 x k ⟨0, by omega⟩ : ℂ) * g x k)
        let L := Real.sqrt ((volume E).toReal⁻¹ * ∫ x in E, ‖u x‖ ^ 2)
        let e := localSpatialEnergy Q t ρ hρ z G V ω
        ∀ (φ : Fin d → Vec d → ℝ) (S : Fin d → Vec d → Mat d)
          (a₀ : Fin d → ℝ) (b₀ : Fin d → Mat d),
          (∀ i, Continuous (φ i)) →
          (∀ i j k, Continuous (fun x => S i x j k)) →
        ∀ H : ℝ,
          (∑ i : Fin d,
            (Real.sqrt ((volume E).toReal⁻¹ * ∫ x in E, |φ i x - a₀ i| ^ 2) +
             Real.sqrt ((volume E).toReal⁻¹ *
               ∫ x in E, frobeniusNorm (S i x - b₀ i) ^ 2))) ≤ H →
        ∀ (ψ : Vec d → ℂ) (A B : ℝ), 0 ≤ A → 0 ≤ B →
          tsupport ψ ⊆ E → (∀ x, ‖ψ x‖ ≤ A) →
          (∀ x k, ‖fderiv ℝ ψ x (unitVector k)‖ ≤ B) →
        ∀ i : Fin d,
        ‖(∫ x, ((φ i x - a₀ i : ℝ) : ℂ) * q x * ψ x) +
          (∫ x, ((φ i x - a₀ i : ℝ) : ℂ) *
            (∑ k : Fin d, (∑ j : Fin d, (ω.1 x k j : ℂ) * F x j) *
              fderiv ℝ ψ x (unitVector k))) -
          (∫ x, ∑ k : Fin d, ∑ j : Fin d,
            ((S i x k j - b₀ i k j : ℝ) : ℂ) * F x j *
              fderiv ℝ ψ x (unitVector k)) +
          (match (generalizing := false) ν with
          | .inr true => 2 * ζ * (∫ x, (∑ k : Fin d,
              ((S i x k ⟨0, by omega⟩ - b₀ i k ⟨0, by omega⟩ : ℝ) : ℂ) *
                g x k) * ψ x)
          | _ => 0)‖ ≤
          (volume E).toReal * H *
            (A * (2 / Real.sqrt (t : ℝ) * e + 2 * ‖c‖ +
                2 * ‖ζ‖ * ((d : ℝ) * M * e)) +
              (d : ℝ) ^ 3 * (M + 1) * B * (e + 2 * ‖ζ‖ * L) +
              2 * ‖ζ‖ * (d : ℝ) * A * e) := by
  classical
  obtain ⟨M₀, A₀, B₀, hM₀, _, _, _, hbound⟩ :=
    node_eq_u2E_reduced_u2D_bounds_of_deps D.ellipticity D.one_le_ellipticity
  obtain ⟨M₁, hM₁, hfields⟩ := carverS_flux_block_actual_endpoint_fields_l2 d hd D
  let M := max M₀ M₁
  have hM : 1 ≤ M := hM₀.trans (le_max_left _ _)
  refine ⟨M, hM, ?_⟩
  intro Q hQ β a μ ζ P Pdag ν t ht ρ hρ z G
  dsimp only
  let U := indexedEndpoint hd Q ν ζ P Pdag β a μ t
  let V := deriv (fun r : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ r.toNNReal)
    (t : ℝ)
  let c := ζ * ∫ ω, ∑ k : Fin d,
    a k ⟨0, by omega⟩ ω * G k ω ∂reducedLaw Q
  let E := {x : Vec d | euclideanNorm (x - z) < ρ}
  let m := volume.restrict E
  let v := Real.sqrt ((volume E).toReal)
  have hv : 0 ≤ v := Real.sqrt_nonneg _
  have hvol := localSpatialEnergy_window_volume z ρ hρ
  have hvmeasure : 0 < m.real Set.univ := by
    simpa only [m, E, measureReal_restrict_apply_univ] using hvol
  have hvsq : v * v = (volume E).toReal := by
    exact Real.mul_self_sqrt (ENNReal.toReal_nonneg)
  have hts : 0 < Real.sqrt (t : ℝ) := Real.sqrt_pos.mpr ht
  filter_upwards [hfields Q hQ β a μ ζ P Pdag ν t ρ hρ z G,
    carverS_flux_block_endpoint_fields_memLp hd D Q hQ ρ hρ z U V G ν ζ c,
    carverS_flux_block_spatial_energy_l2 Q t ρ hρ z G V,
    (hbound d D.dependenceRange Q).2.2] with ω hquant hmem henergy hω
  let u := fun x : Vec d => U (translate x ω)
  let g := fun (x : Vec d) (j : Fin d) => G j (translate x ω)
  let F := fun (x : Vec d) (j : Fin d) => g x j -
    match (generalizing := false) ν with
    | .inr true => 2 * ζ * (unitVector (⟨0, by omega⟩ : Fin d) j : ℂ) * u x
    | _ => 0
  let q := fun x : Vec d => 2 * V (translate x ω) +
    match (generalizing := false) ν with
    | .inr true => 0
    | _ => 2 * c - 2 * ζ * (∑ k : Fin d,
        (ω.1 x k ⟨0, by omega⟩ : ℂ) * g x k)
  let L := Real.sqrt ((volume E).toReal⁻¹ * ∫ x in E, ‖u x‖ ^ 2)
  let e := localSpatialEnergy Q t ρ hρ z G V ω
  have he : 0 ≤ e := Real.sqrt_nonneg _
  have hL : 0 ≤ L := Real.sqrt_nonneg _
  have hnormu : Calculus.S1.l2Size m u = v * L := by
    simpa only [m, measureReal_restrict_apply_univ, measureReal_def, Measure.restrict_apply_univ, v, L] using
      carverS_flux_block_l2Size_normalized (f := u) m hvmeasure
  have hnormv : Calculus.S1.l2Size m (fun x => V (translate x ω)) ≤
      v * (e / Real.sqrt (t : ℝ)) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hts).mpr
    simpa only [m, E, e, v, measureReal_def, mul_comm] using henergy.2.2.2
  have hnormg : Calculus.S1.l2Size m
      (fun x => Real.sqrt (∑ j : Fin d, ‖g x j‖ ^ 2)) ≤ v * e := henergy.2.2.1
  have hnormF : Calculus.S1.l2Size m
      (fun x => Real.sqrt (∑ j : Fin d, ‖F x j‖ ^ 2)) ≤
      v * ((d : ℝ) * (e + 2 * ‖ζ‖ * L)) := by
    calc
      _ ≤ (d : ℝ) * (Calculus.S1.l2Size m
          (fun x => Real.sqrt (∑ j : Fin d, ‖g x j‖ ^ 2)) +
          2 * ‖ζ‖ * Calculus.S1.l2Size m u) := hquant.1
      _ ≤ (d : ℝ) * (v * e + 2 * ‖ζ‖ * (v * L)) :=
        mul_le_mul_of_nonneg_left
          (add_le_add hnormg (by rw [hnormu])) (Nat.cast_nonneg d)
      _ = _ := by ring
  have hnormq : Calculus.S1.l2Size m q ≤
      v * (2 / Real.sqrt (t : ℝ) * e + 2 * ‖c‖ +
        2 * ‖ζ‖ * ((d : ℝ) * M * e)) := by
    have hM₁M : M₁ ≤ M := le_max_right _ _
    have hcoeff : (d : ℝ) * M₁ * Calculus.S1.l2Size m
        (fun x => Real.sqrt (∑ j : Fin d, ‖g x j‖ ^ 2)) ≤
        (d : ℝ) * M * (v * e) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hM₁M (Nat.cast_nonneg d)) hnormg
        (Calculus.S1.l2Size_nonneg _) (mul_nonneg (Nat.cast_nonneg d) (zero_le_one.trans hM))
    calc
      _ ≤ 2 * Calculus.S1.l2Size m (fun x => V (translate x ω)) +
          2 * ‖c‖ * v + 2 * ‖ζ‖ * ((d : ℝ) * M₁ *
            Calculus.S1.l2Size m (fun x => Real.sqrt (∑ j : Fin d, ‖g x j‖ ^ 2))) := by
        simpa only [m, E, measureReal_restrict_apply_univ, measureReal_def, Measure.restrict_apply_univ, v] using hquant.2
      _ ≤ 2 * (v * (e / Real.sqrt (t : ℝ))) + 2 * ‖c‖ * v +
          2 * ‖ζ‖ * ((d : ℝ) * M * (v * e)) :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left hnormv (by norm_num)) le_rfl)
          (mul_le_mul_of_nonneg_left hcoeff (by positivity))
      _ = _ := by ring
  intro φ S a₀ b₀ hφ hS H hosc ψ A B hA hB hsupp hψ hDψ i
  obtain ⟨hφm, hSm, hsize⟩ :=
    carverS_flux_block_centered_corrector_l2 φ S a₀ b₀ hφ hS z ρ hρ H hosc i
  let ζν : ℂ := match (generalizing := false) ν with | .inr true => ζ | _ => 0
  have hζν : ‖ζν‖ ≤ ‖ζ‖ := by
    dsimp only [ζν]
    split
    · exact le_rfl
    · simpa only [norm_zero] using norm_nonneg ζ
  have hidentity := carverS_flux_block_identity_l2_bound m
    (fun x => φ i x - a₀ i) (fun x => S i x - b₀ i)
    (fun x k j => ω.1 x k j) F g q ψ ζν ⟨0, by omega⟩
    hφm hSm hmem.2.2.2.2 hmem.2.2.2.1 henergy.1
    A B M hA hB (zero_le_one.trans hM)
    (Filter.Eventually.of_forall fun x k j =>
      (abs_apply_le_of_isElliptic (zero_lt_one.trans_le hM₀) hω.1 x k j).trans
        (le_max_left _ _))
    (Filter.Eventually.of_forall hψ) (Filter.Eventually.of_forall hDψ)
  have hcombined := carverS_two_corrector_sizes_bound
    (Calculus.S1.l2Size m (fun x => φ i x - a₀ i))
    (Calculus.S1.l2Size m (fun x => frobeniusNorm (S i x - b₀ i)))
    (v * H) A B M ‖ζν‖ d (Calculus.S1.l2Size m q)
    (Calculus.S1.l2Size m (fun x => Real.sqrt (∑ j : Fin d, ‖F x j‖ ^ 2)))
    (Calculus.S1.l2Size m (fun x => Real.sqrt (∑ j : Fin d, ‖g x j‖ ^ 2)))
    (Calculus.S1.l2Size_nonneg _) (Calculus.S1.l2Size_nonneg _) hA hB
    (zero_le_one.trans hM) (norm_nonneg _) (Nat.cast_nonneg d)
    (Calculus.S1.l2Size_nonneg _) (Calculus.S1.l2Size_nonneg _)
    (Calculus.S1.l2Size_nonneg _) hsize
  have hH : 0 ≤ H := by
    have hsum : 0 ≤ ∑ i : Fin d,
        (Real.sqrt ((volume E).toReal⁻¹ * ∫ x in E, |φ i x - a₀ i| ^ 2) +
          Real.sqrt ((volume E).toReal⁻¹ *
            ∫ x in E, frobeniusNorm (S i x - b₀ i) ^ 2)) :=
      Finset.sum_nonneg fun _ _ => add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    exact hsum.trans hosc
  have hweights := add_le_add
    (add_le_add (mul_le_mul_of_nonneg_left hnormq hA)
      (mul_le_mul_of_nonneg_left hnormF
        (by positivity : 0 ≤ (d : ℝ) ^ 2 * (M + 1) * B)))
    (mul_le_mul
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hζν (by norm_num : (0 : ℝ) ≤ 2))
          (Nat.cast_nonneg d)) hA) hnormg
      (Calculus.S1.l2Size_nonneg _) (by positivity : 0 ≤ 2 * ‖ζ‖ * (d : ℝ) * A))
  have hresult := (hidentity.trans hcombined).trans
    (mul_le_mul_of_nonneg_left hweights (mul_nonneg hv hH))
  have hlocal := carverS_flux_block_identity_localization E
    (fun x => φ i x - a₀ i) (fun x => S i x - b₀ i) ω.1 F g q ψ ζν
    ⟨0, by omega⟩ hsupp
  have hlast : (match (generalizing := false) ν with
      | .inr true => 2 * ζ * (∫ x, (∑ k : Fin d,
          ((S i x k ⟨0, by omega⟩ - b₀ i k ⟨0, by omega⟩ : ℝ) : ℂ) * g x k) * ψ x)
      | _ => 0) = 2 * ζν * (∫ x, (∑ k : Fin d,
        ((S i x k ⟨0, by omega⟩ - b₀ i k ⟨0, by omega⟩ : ℝ) : ℂ) * g x k) * ψ x) := by
    dsimp only [ζν]
    split <;> simp only [mul_zero, zero_mul]
  rw [hlast]
  change ‖_‖ ≤ _
  simp only [Matrix.sub_apply] at hlocal hresult
  rw [hlocal]
  convert hresult using 1
  dsimp only [e, c, L, E, u, U, V]
  rw [← hvsq]
  ring

/-- Stationarity bounds the normalized local value on the same open window used
by the flux identity, uniformly in its positive radius and center. -/
theorem carverS_flux_block_local_value_moment {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (U : Lp ℂ 2 (reducedLaw Q))
    (p : ℝ) (hp : 2 ≤ p) (hU : MemLp U (ENNReal.ofReal p) (reducedLaw Q))
    (ρ : ℝ) (hρ : 0 < ρ) (z : Vec d) :
    let E := {x : Vec d | euclideanNorm (x - z) < ρ}
    let L := fun ω : FieldPair d => Real.sqrt
      ((volume E).toReal⁻¹ * ∫ x in E, ‖U (translate x ω)‖ ^ 2)
    MemLp L (ENNReal.ofReal p) (reducedLaw Q) ∧
      (eLpNorm L (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        (eLpNorm U (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  let E := {x : Vec d | euclideanNorm (x - z) < ρ}
  have hv : 0 < (volume E).toReal := localSpatialEnergy_window_volume z ρ hρ
  have hv0 : volume E ≠ 0 := (ENNReal.toReal_pos_iff.mp hv).1.ne'
  have hvfin : volume E ≠ ∞ := (ENNReal.toReal_pos_iff.mp hv).2.ne
  let κ : Measure (Vec d) := (volume E)⁻¹ • volume.restrict E
  let : IsProbabilityMeasure κ := ⟨by
    dsimp [κ]
    rw [Measure.restrict_apply_univ]
    exact ENNReal.inv_mul_cancel hv0 hvfin⟩
  obtain ⟨hL, hnorm⟩ := local_time_stationary_square_average_memLp Q
    (Measure.dirac (0 : ℝ)) κ p (eLpNorm U (ENNReal.ofReal p) (reducedLaw Q)).toReal
    hp ENNReal.toReal_nonneg (fun q => U q.2)
    ((Lp.stronglyMeasurable U).measurable.comp measurable_snd)
    (Filter.Eventually.of_forall fun _ => ⟨hU, le_rfl⟩)
  have heq (ω : FieldPair d) :
      (∫ s : ℝ, ∫ x, ‖U (translate x ω)‖ ^ 2 ∂κ ∂Measure.dirac 0) =
        (volume E).toReal⁻¹ * ∫ x in E, ‖U (translate x ω)‖ ^ 2 := by
    rw [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
    simp only [κ, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]
  simp only [heq] at hL hnorm
  exact ⟨hL, hnorm⟩

/-- Stationary square averages over the closed Euclidean window are controlled
by the finite-p norm of the actual field. -/
theorem carverS_flux_block_closed_local_value_moment {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (U : Lp ℂ 2 (reducedLaw Q))
    (p : ℝ) (hp : 2 ≤ p) (hU : MemLp U (ENNReal.ofReal p) (reducedLaw Q))
    (ρ : ℝ) (hρ : 0 < ρ) (z : Vec d) :
    let E := {x : Vec d | euclideanNorm (x - z) ≤ ρ}
    let L := fun ω : FieldPair d => Real.sqrt
      (⨍ x in E, ‖U (translate x ω)‖ ^ 2)
    MemLp L (ENNReal.ofReal p) (reducedLaw Q) ∧
      (eLpNorm L (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        (eLpNorm U (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  let E := {x : Vec d | euclideanNorm (x - z) ≤ ρ}
  have hball : E = PDE.euclideanClosedBall z ρ := by
    ext x
    change Real.sqrt (euclideanSq (x - z)) ≤ ρ ↔ PDE.vecNormSq (x - z) ≤ ρ ^ 2
    rw [Real.sqrt_le_iff]
    exact and_iff_right hρ.le
  have hv0 : volume E ≠ 0 := ne_of_gt
    ((PDE.volume_euclideanBall_pos z hρ).trans_le
      (measure_mono (by rw [hball]; exact PDE.euclideanBall_subset_euclideanClosedBall z ρ)))
  have hvfin : volume E ≠ ∞ := (isCompact_physical_euclidean_closedBall z ρ).measure_ne_top
  let κ : Measure (Vec d) := (volume E)⁻¹ • volume.restrict E
  let : IsProbabilityMeasure κ := ⟨by
    dsimp [κ]
    rw [Measure.restrict_apply_univ]
    exact ENNReal.inv_mul_cancel hv0 hvfin⟩
  obtain ⟨hL, hnorm⟩ := local_time_stationary_square_average_memLp Q
    (Measure.dirac (0 : ℝ)) κ p (eLpNorm U (ENNReal.ofReal p) (reducedLaw Q)).toReal
    hp ENNReal.toReal_nonneg (fun q => U q.2)
    ((Lp.stronglyMeasurable U).measurable.comp measurable_snd)
    (Filter.Eventually.of_forall fun _ => ⟨hU, le_rfl⟩)
  have heq (ω : FieldPair d) :
      (∫ s : ℝ, ∫ x, ‖U (translate x ω)‖ ^ 2 ∂κ ∂Measure.dirac 0) =
        ⨍ x in E, ‖U (translate x ω)‖ ^ 2 := by
    rw [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
    simp only [average_eq', Measure.restrict_apply_univ]
    rfl
  simp only [heq] at hL hnorm
  exact ⟨hL, hnorm⟩

/-- Actual endpoints have finite moments of every order at least two. -/
theorem carverS_flux_block_actual_endpoint_memLp
    {d : ℕ} (hd : 2 ≤ d) {D : StructuralData d} (p : ℝ) (hp : 2 ≤ p)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β)
    (ha : IsReducedCoefficientObservation Q a)
    (hμ : IsReducedClockObservation Q μ) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    (ν : EndpointIndex d) (t : ℝ≥0) :
    MemLp (indexedEndpoint hd Q ν ζ P Pdag β a μ t)
      (ENNReal.ofReal p) (reducedLaw Q) := by
  let := reducedLaw_probability Q
  let r : ℝ := p / 2 - 1
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have hpr : 2 * (1 + r) = p := by dsimp [r]; ring
  have hforward (f : Lp ℂ 2 (reducedLaw Q))
      (hf : MemLp f (ENNReal.ofReal p) (reducedLaw Q)) :
      MemLp (P t f) (ENNReal.ofReal p) (reducedLaw Q) := by
    have hf' : MemLp f (ENNReal.ofReal (2 * (1 + r))) (reducedLaw Q) := by
      rwa [hpr]
    have h := (hP.power_moment_growth hr f hf' t).1
    rwa [hpr] at h
  have htranspose (f : Lp ℂ 2 (reducedLaw Q))
      (hf : MemLp f (ENNReal.ofReal p) (reducedLaw Q)) :
      MemLp (Pdag t f) (ENNReal.ofReal p) (reducedLaw Q) := by
    have hf' : MemLp f (ENNReal.ofReal (2 * (1 + r))) (reducedLaw Q) := by
      rwa [hpr]
    have h := (hPdag.power_moment_growth hP hr f hf' t).1
    rwa [hpr] at h
  obtain ⟨K, _hK, hobs⟩ := EndpointFiniteP.observation_bounds d D
  obtain ⟨hb, ha', hm⟩ := hobs Q hQ β a μ hβ ha hμ
  have hβp (j : Fin d) : MemLp (β j) (ENNReal.ofReal p) (reducedLaw Q) :=
    MemLp.of_bound (Lp.memLp (β j)).aestronglyMeasurable K (hb j)
  have hap (j k : Fin d) : MemLp (a j k) (ENNReal.ofReal p) (reducedLaw Q) :=
    MemLp.of_bound (Lp.memLp (a j k)).aestronglyMeasurable K (ha' j k)
  have hμp : MemLp μ (ENNReal.ofReal p) (reducedLaw Q) :=
    MemLp.of_bound (Lp.memLp μ).aestronglyMeasurable K hm
  have hsmul (f : Lp ℂ 2 (reducedLaw Q))
      (hf : MemLp f (ENNReal.ofReal p) (reducedLaw Q)) :
      MemLp (ζ • f) (ENNReal.ofReal p) (reducedLaw Q) :=
    (memLp_congr_ae (Lp.coeFn_smul ζ f)).2 (hf.const_smul ζ)
  have hcenter (f : Lp ℂ 2 (reducedLaw Q))
      (hf : MemLp f (ENNReal.ofReal p) (reducedLaw Q)) :
      MemLp (centeredComplexLp Q f) (ENNReal.ofReal p) (reducedLaw Q) :=
    (memLp_congr_ae (coeFn_centeredComplexLp Q f)).2 (hf.sub (memLp_const _))
  cases ν with
  | inl k =>
    have hinit : MemLp (β k + ζ • a ⟨0, by omega⟩ k)
        (ENNReal.ofReal p) (reducedLaw Q) :=
      (memLp_congr_ae (Lp.coeFn_add _ _)).2 ((hβp k).add (hsmul _ (hap _ k)))
    exact hcenter _ (hforward _ hinit)
  | inr b =>
    cases b with
    | false => exact hsmul _ (hcenter _ (hforward μ hμp))
    | true => exact htranspose _ (hβp ⟨0, by omega⟩)

/-- Centering costs at most two in a finite-p norm. -/
theorem carverS_flux_block_centered_norm_le {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (f : Lp ℂ 2 (reducedLaw Q))
    {p : ℝ} (hp : 1 ≤ p)
    (hf : MemLp (f : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)) :
    (eLpNorm (centeredComplexLp Q f : FieldPair d → ℂ)
      (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
      2 * (eLpNorm (f : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  let := reducedLaw_probability Q
  have hq : (1 : ENNReal) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hp
  let m : ℂ := ∫ ω, f ω ∂reducedLaw Q
  have hm : eLpNorm (fun _ : FieldPair d => m) (ENNReal.ofReal p) (reducedLaw Q) ≤
      eLpNorm (f : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) := by
    rw [eLpNorm_const _ (ne_zero_of_lt (lt_of_lt_of_le zero_lt_one hq))
      (NeZero.ne (reducedLaw Q)), measure_univ, ENNReal.one_rpow, mul_one]
    exact (enorm_integral_le_lintegral_enorm _).trans
      ((eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable).symm.le.trans
        (eLpNorm_le_eLpNorm_of_exponent_le hq))
  have hsub := EinsteinFull.Calculus.K5.toReal_eLpNorm_sub_le hq hf
    (memLp_const m)
  rw [eLpNorm_congr_ae (coeFn_centeredComplexLp Q f)]
  exact hsub.trans (by
    have hm' := ENNReal.toReal_mono hf.eLpNorm_ne_top hm
    change _ ≤ _ at hm'
    linarith)

/-- Uniform finite-p growth of the actual late-interval evolution. -/
theorem carverS_flux_block_late_endpoint_growth (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) (p : ℝ) (hp : 2 ≤ p) :
    ∃ Cp : ℝ, 0 < Cp ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (ζ : ℂ)
      (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ (ν : EndpointIndex d)
      (f : Lp ℂ 2 (reducedLaw Q)), MemLp f (ENNReal.ofReal p) (reducedLaw Q) →
      ∀ t : ℝ≥0,
      (eLpNorm (lateEndpointEvolution Q ν P Pdag t f : FieldPair d → ℂ)
        (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        2 * Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
          (eLpNorm f (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  let a : ℝ := p / 2 - 1
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hpa : 2 * (1 + a) = p := by dsimp [a]; ring
  let K := Real.exp (2 * D.ellipticity) * D.ellipticity
  let cF := (d : ℝ) * K * K ^ 2
  let cT := (d : ℝ) * K * (K * (1 + 2 * a)) ^ 2
  have hK : 0 ≤ K := mul_nonneg (Real.exp_pos _).le
    (zero_le_one.trans D.one_le_ellipticity)
  have hd0 : 0 ≤ (d : ℝ) := by exact_mod_cast (Nat.zero_le d)
  have hcF : 0 ≤ cF := mul_nonneg (mul_nonneg hd0 hK) (sq_nonneg _)
  have hcT : 0 ≤ cT := mul_nonneg (mul_nonneg hd0 hK) (sq_nonneg _)
  refine ⟨cF + cT + 1, by positivity, ?_⟩
  intro Q ζ P Pdag hP hPdag ν f hf t
  have hf' : MemLp f (ENNReal.ofReal (2 * (1 + a))) (reducedLaw Q) := by rwa [hpa]
  have hforward := (hP.power_moment_growth ha f hf' t).1
  rw [hpa] at hforward
  have hgF := hP.eLpNorm_growth ha f hf' t
  have hgT := hPdag.eLpNorm_growth hP ha f hf' t
  rw [hpa] at hgF hgT
  have hrF : ((d : ℝ) * K * (‖ζ‖ * K) ^ 2) * (t : ℝ) =
      cF * ‖ζ‖ ^ 2 * (t : ℝ) := by dsimp [cF]; ring
  have hrT : ((d : ℝ) * K * (‖ζ‖ * K * (1 + 2 * a)) ^ 2) * (t : ℝ) =
      cT * ‖ζ‖ ^ 2 * (t : ℝ) := by dsimp [cT]; ring
  change eLpNorm (P t f) (ENNReal.ofReal p) (reducedLaw Q) ≤
    eLpNorm f (ENNReal.ofReal p) (reducedLaw Q) *
      ENNReal.ofReal (Real.exp (((d : ℝ) * K * (‖ζ‖ * K) ^ 2) * (t : ℝ))) at hgF
  change eLpNorm (Pdag t f) (ENNReal.ofReal p) (reducedLaw Q) ≤
    eLpNorm f (ENNReal.ofReal p) (reducedLaw Q) * ENNReal.ofReal
      (Real.exp (((d : ℝ) * K * (‖ζ‖ * K * (1 + 2 * a)) ^ 2) * (t : ℝ))) at hgT
  rw [hrF] at hgF
  rw [hrT] at hgT
  have hF := ENNReal.toReal_mono (ENNReal.mul_ne_top hf.ne_top ENNReal.ofReal_ne_top) hgF
  have hT := ENNReal.toReal_mono (ENNReal.mul_ne_top hf.ne_top ENNReal.ofReal_ne_top) hgT
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] at hF hT
  have hfac : 0 ≤ ‖ζ‖ ^ 2 * (t : ℝ) := mul_nonneg (sq_nonneg _) t.coe_nonneg
  have heF : Real.exp (cF * ‖ζ‖ ^ 2 * (t : ℝ)) ≤
      Real.exp ((cF + cT + 1) * ‖ζ‖ ^ 2 * (t : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (show 0 ≤ cT + 1 by positivity) hfac]
  have heT : Real.exp (cT * ‖ζ‖ ^ 2 * (t : ℝ)) ≤
      Real.exp ((cF + cT + 1) * ‖ζ‖ ^ 2 * (t : ℝ)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (show 0 ≤ cF + 1 by positivity) hfac]
  have hnorm : 0 ≤ (eLpNorm f (ENNReal.ofReal p) (reducedLaw Q)).toReal := ENNReal.toReal_nonneg
  have hF' := hF.trans (mul_le_mul_of_nonneg_left heF hnorm)
  have hT' := hT.trans (mul_le_mul_of_nonneg_left heT hnorm)
  cases ν with
  | inl j =>
    simp only [lateEndpointEvolution, ContinuousLinearMap.comp_apply,
      centeredComplexLpCLM_apply]
    have hc := carverS_flux_block_centered_norm_le Q (P t f) (by linarith : 1 ≤ p) hforward
    nlinarith [mul_nonneg hnorm (Real.exp_pos ((cF + cT + 1) * ‖ζ‖ ^ 2 * (t : ℝ))).le]
  | inr b =>
    cases b with
    | false =>
      simp only [lateEndpointEvolution, ContinuousLinearMap.comp_apply,
        centeredComplexLpCLM_apply]
      have hc := carverS_flux_block_centered_norm_le Q (P t f) (by linarith : 1 ≤ p) hforward
      nlinarith [mul_nonneg hnorm (Real.exp_pos ((cF + cT + 1) * ‖ζ‖ ^ 2 * (t : ℝ))).le]
    | true =>
      change (eLpNorm (Pdag t f : FieldPair d → ℂ) _ _).toReal ≤ _
      nlinarith [mul_nonneg hnorm (Real.exp_pos ((cF + cT + 1) * ‖ζ‖ ^ 2 * (t : ℝ))).le]

/-- Actual terminal local averages are bounded by the earlier endpoint. -/
theorem carverS_flux_block_actual_terminal_local_value_moment
    (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) (p : ℝ) (hp : 2 ≤ p) :
    ∃ C Cp : ℝ, 1 ≤ C ∧ 0 < Cp ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
    ∀ (t : ℝ≥0) (ht : 0 < (t : ℝ)) (ρ : ℝ) (z : Vec d),
      Real.sqrt (t : ℝ) ≤ ρ →
      let L := fun ω : FieldPair d => Real.sqrt
        (⨍ x in {x : Vec d | euclideanNorm (x - z) ≤ ρ},
          ‖indexedEndpoint hd Q ν ζ P Pdag β a μ t (translate x ω)‖ ^ 2)
      MemLp L (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm L (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
          C * (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C *
            Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
            (eLpNorm (indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8) :
              FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal := by
  obtain ⟨Cp, hCp, hgrowth⟩ := carverS_flux_block_late_endpoint_growth d hd D p hp
  refine ⟨2, Cp, by norm_num, hCp, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν t ht ρ z hρ
  have hρ' : 0 < ρ := (Real.sqrt_pos.mpr ht).trans_le hρ
  have hU := carverS_flux_block_actual_endpoint_memLp hd p hp Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν t
  have hV := carverS_flux_block_actual_endpoint_memLp hd p hp Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν (t / 8)
  obtain ⟨hL, hLnorm⟩ := carverS_flux_block_closed_local_value_moment Q
    (indexedEndpoint hd Q ν ζ P Pdag β a μ t) p hp hU ρ hρ' z
  refine ⟨hL, hLnorm.trans ?_⟩
  have h8 : t / 8 ≤ t := div_le_self zero_le (by norm_num)
  have hsum : t / 8 + (t - t / 8) = t := by rw [add_comm, tsub_add_cancel_of_le h8]
  have hrestart := hP.indexedEndpoint_add hd hPdag β a μ ν (t / 8) (t - t / 8)
  rw [hsum] at hrestart
  have hg := hgrowth Q ζ P Pdag hP hPdag ν
    (indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8)) hV (t - t / 8)
  rw [← hrestart] at hg
  have htime : ((t - t / 8 : ℝ≥0) : ℝ) ≤ (t : ℝ) := by
    exact_mod_cast (tsub_le_self : t - t / 8 ≤ t)
  have he : Real.exp (Cp * ‖ζ‖ ^ 2 * ((t - t / 8 : ℝ≥0) : ℝ)) ≤
      Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left htime (mul_nonneg hCp.le (sq_nonneg _))
  have hbase : 1 ≤ 1 + ‖ζ‖ * Real.sqrt (t : ℝ) :=
    le_add_of_nonneg_right (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
  have hpow : 1 ≤ (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ (2 : ℝ) :=
    Real.one_le_rpow hbase (by norm_num)
  have hn : 0 ≤ (eLpNorm (indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8) :
      FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal := ENNReal.toReal_nonneg
  have hexp := (Real.exp_pos (Cp * ‖ζ‖ ^ 2 * (t : ℝ))).le
  exact hg.trans (by nlinarith [mul_nonneg hn hexp,
    mul_le_mul_of_nonneg_right he hn,
    mul_le_mul_of_nonneg_right hpow (mul_nonneg hn hexp)])

end EinsteinFull.Blueprint

#print axioms EinsteinFull.Blueprint.carverS_transpose_terminal_local_value_moment
#print axioms EinsteinFull.Blueprint.carverS_flux_block_skew_local_oscillation
#print axioms EinsteinFull.Blueprint.carverS_flux_block_selected_pair

#print axioms EinsteinFull.Blueprint.carverS_flux_block_gaussian_envelope
#print axioms EinsteinFull.Blueprint.carverS_flux_block_gaussian_spatial_sup
#print axioms EinsteinFull.Blueprint.carverS_flux_block_identity_l2_bound
#print axioms EinsteinFull.Blueprint.carverS_flux_block_l2Size_normalized
#print axioms EinsteinFull.Blueprint.carverS_flux_block_cutoff_kernel_derivative_bound

#print axioms EinsteinFull.Blueprint.carverS_flux_block_centered_corrector_l2

#print axioms EinsteinFull.Blueprint.carverS_flux_block_identity_localization

#print axioms EinsteinFull.Blueprint.carverS_flux_block_spatial_energy_l2

#print axioms EinsteinFull.Blueprint.carverS_flux_block_cutoff_test_support

#print axioms EinsteinFull.Blueprint.carverS_flux_block_local_time_on_flux_witness

#print axioms EinsteinFull.Blueprint.carverS_flux_block_endpoint_fields_memLp

#print axioms EinsteinFull.Blueprint.carverS_flux_block_endpoint_fields_l2

#print axioms EinsteinFull.Blueprint.carverS_flux_block_actual_endpoint_fields_l2

#print axioms EinsteinFull.Blueprint.carverS_flux_block_centering_integral_bound

#print axioms EinsteinFull.Blueprint.carverS_flux_block_global_gradient_l2_le_energy

#print axioms EinsteinFull.Blueprint.carverS_flux_block_centering_integral_le_energy

#print axioms EinsteinFull.Blueprint.carverS_flux_block_actual_identity_oscillation_bound

#print axioms EinsteinFull.Blueprint.carverS_flux_block_local_value_moment

#print axioms EinsteinFull.Blueprint.carverS_flux_block_closed_local_value_moment

#print axioms EinsteinFull.Blueprint.carverS_flux_block_actual_endpoint_memLp


#print axioms EinsteinFull.Blueprint.carverS_flux_block_centered_norm_le

#print axioms EinsteinFull.Blueprint.carverS_flux_block_late_endpoint_growth

#print axioms EinsteinFull.Blueprint.carverS_flux_block_actual_terminal_local_value_moment
