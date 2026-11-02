import EinsteinFull.Blueprint.G4.node_sharp_u2E_example_u23_smooth_u2D_seed
import EinsteinFull.Blueprint.G4.node_app_u3A_sharp_u2D_fields
import EinsteinFull.Blueprint.G4.node_app_u3A_sharp_u2D_harmonic
import EinsteinFull.Blueprint.G4.node_app_u3A_sharp_u2D_clock
import EinsteinFull.Blueprint.G4.node_eq_u2E_time_u2D_change_u2D_identities
import EinsteinFull.Blueprint.G4.node_sharp_u2E_example_u23_seed_u2D_nonconstancy
import EinsteinFull.Blueprint.G4.node_sharp_u2E_example_u23_seed_u2D_ergodicity
import EinsteinFull.Blueprint.G4.node_sharp_u2E_example_u23_clock_u2D_continuity
import EinsteinFull.Blueprint.G4.node_sharp_u2E_example_u23_positive_u2D_coefficient
import EinsteinFull.Calculus.S4SharpDetSupport
import EinsteinFull.Calculus.S2ForwardFamily
import EinsteinFull.Calculus.S2PositiveCoefficientSupport
import EinsteinFull.Blueprint.Foundation.Draft.S2SmoothScopeTimeChange

/-! Reduction of graph node `sharp.example#positive-coefficient` (`paper/main.tex:1567–1572`) to
its eight graph dependencies.  Conjuncts 1–4 are the deterministic and environment-level
identities (`sharpPositive_environment`, `reducedCoefficient_diagonal`).  Conjunct 5 builds the
reduced family `Y` from the signed physical family `X` by the forward time change
(`exists_reducedFamily_of_signedPhysical`), identifies the reduced velocity from `app:sharp-harmonic`,
the clock rate from `eq.time-change-identities` and `app:sharp-clock`, and the right-hand limit of
the time average from `sharp.example#clock-continuity`. -/

open MeasureTheory Filter
open scoped Topology NNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.Sharpness

@[nolint unusedArguments]
theorem node_sharp_u2E_example_u23_positive_u2D_coefficient_of_deps
    (_hseed : node_sharp_u2E_example_u23_smooth_u2D_seedStmt)
    (hfields : node_app_u3A_sharp_u2D_fieldsStmt)
    (hharm : node_app_u3A_sharp_u2D_harmonicStmt)
    (hclock : node_app_u3A_sharp_u2D_clockStmt)
    (htc : node_eq_u2E_time_u2D_change_u2D_identitiesStmtV2)
    (_hnonconst : node_sharp_u2E_example_u23_seed_u2D_nonconstancyStmt)
    (_herg : node_sharp_u2E_example_u23_seed_u2D_ergodicityStmt)
    (hcc : node_sharp_u2E_example_u23_clock_u2D_continuityStmt) :
    node_sharp_u2E_example_u23_positive_u2D_coefficientStmt := by
  intro d hd P hP first D Q hQ
  have : IsProbabilityMeasure P := hP.1
  obtain ⟨hp1, hp2, hp3, hp4⟩ := sharpPositive_environment hd hP Q hQ
  have hδ : 0 < EinsteinFull.Work.W8.clockParameter first :=
    EinsteinFull.Work.W8.clockParameter_pos first
  refine ⟨fun W x => ?_, hp1, ?_⟩
  · intro ψ
    exact EinsteinFull.Work.W8.reducedCoefficient_diagonal first W x
  intro δ c₀
  have hc0 : c₀ = δ * ((∫ ω, reducedCoefficient ω 0 first first ∂Q.measure) - 1) := by
    show EinsteinFull.Work.W8.clockParameter first * (∫ W, euclideanSq
        (gradient (EinsteinFull.Work.W8.corrector W) 0) /
          (1 + gradient (EinsteinFull.Work.W8.corrector W) 0 first) ∂P) =
      EinsteinFull.Work.W8.clockParameter first *
        ((∫ ω, reducedCoefficient ω 0 first first ∂Q.measure) - 1)
    rw [hp3]
  refine ⟨mul_pos hδ hp2, hc0, ?_⟩
  intro X hX covariance hcov velocity hvel
  have hsm : ∀ᵐ ω ∂Q.measure, IsSmoothFieldPair ω := by
    rw [hQ]
    exact (ae_map_iff (EinsteinFull.Work.W8.measurable_physicalPair first).aemeasurable
      measurableSet_isSmoothFieldPair_fieldPair).2
      (ae_of_all _ (EinsteinFull.Work.W8.physicalPair_isSmooth first))
  obtain ⟨Y, hYmp, hYrel⟩ :=
    EinsteinFull.exists_reducedFamily_of_signedPhysical first Q hsm X hX
  obtain ⟨-, -, hcovs, hvels⟩ := hharm d hd P hP D Q hQ
  have hcov1 : covariance.mulVec (unitVector first) = unitVector first := hcovs X hX covariance hcov
  obtain ⟨-, hclk⟩ := hclock d hd P hP D Q hQ
  obtain ⟨avg, havgY, havgLim⟩ := hcc d hd P hP D Q hQ Y (fun lam _ => hYmp lam)
  obtain ⟨Λ, hΛ1, hΛ⟩ := htc D.ellipticity Q.ellipticity_parameter
  obtain ⟨-, -, D₀, -, -, -, hQ₀⟩ := hfields d hd
  obtain ⟨Q₀, hQ₀m, hQ₀s, -⟩ := hQ₀ P hP
  have hsmb : ∀ᵐ ω ∂Q.measure, IsSmoothWithBounds D₀.derivativeBound ω := by
    rw [hQ, ← hQ₀m]
    exact hQ₀s
  obtain ⟨htc1, -, -⟩ := hΛ d hd D.dependenceRange D₀.derivativeBound Q
    D.one_le_dependenceRange D₀.derivativeBound_pos hsmb X Y hX hYmp hYrel
  have hlim := EinsteinFull.tendsto_sharp_expansion (EinsteinFull.Work.W8.clockParameter first)
    (∫ ω, reducedCoefficient ω 0 first first ∂Q.measure) avg havgLim
  have hlim' : Tendsto (fun lam : ℝ => EinsteinFull.Work.W8.clockParameter first * (avg lam - 1) /
      (1 - EinsteinFull.Work.W8.clockParameter first * lam * (avg lam - 1))) (𝓝[>] (0 : ℝ))
      (𝓝 c₀) := by
    rw [hc0]
    exact hlim
  refine hlim'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with lam hlam
  have hlam' : 0 < lam := hlam
  obtain ⟨η, vX, vY, hηlo, -, hrate, hvX, hvY, hrel⟩ := htc1 lam hlam'.ne'
  obtain ⟨ell, hell, hellfirst⟩ := hvels lam hlam'.ne' (Y lam) (hYmp lam)
  obtain ⟨η', avg', hrate', hηeq, havg', -⟩ := hclk lam hlam'.ne' (Y lam) (hYmp lam)
  have hprobY : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw (Y lam) ω) := by
    filter_upwards [hYmp lam] with ω h
    exact h.1
  have hprobX : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw (X lam) ω) := by
    filter_upwards [hX lam] with ω h
    exact h.1
  have hvY_eq : vY = ell := by
    refine EinsteinFull.eq_of_quenched_ae hprobY ?_
    filter_upwards [hvY, hell] with ω h1 h2
    filter_upwards [h1, h2] with γ a b
    exact HasPathVelocity.unique a b
  have hvX_eq : vX = velocity lam := by
    refine EinsteinFull.eq_of_quenched_ae hprobX ?_
    filter_upwards [hvX, hvel lam hlam'] with ω h1 h2
    filter_upwards [h1, h2] with γ a b
    exact HasPathVelocity.unique a b
  have hη_eq : η = η' := by
    refine EinsteinFull.eq_of_quenched_ae hprobY ?_
    filter_upwards [hrate, hrate'] with ω h1 h2
    filter_upwards [h1, h2] with γ a b
    exact tendsto_nhds_unique a b
  have havg_eq : avg' = avg lam := by
    refine EinsteinFull.eq_of_quenched_ae hprobY ?_
    filter_upwards [havg', havgY lam hlam'] with ω h1 h2
    filter_upwards [h1, h2] with γ a b
    exact tendsto_nhds_unique a b
  have hηpos : η ≠ 0 :=
    (lt_of_lt_of_le (inv_pos.2 (lt_of_lt_of_le one_pos hΛ1)) hηlo).ne'
  have hη : η = 1 - EinsteinFull.Work.W8.clockParameter first * lam * (avg lam - 1) := by
    rw [hη_eq, hηeq, havg_eq]
  have hvfirst : velocity lam first = η⁻¹ * lam := by
    rw [← hvX_eq, hrel, hvY_eq]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [show ell first = lam from hellfirst]
  have hone : (unitVector first : Vec d) first = 1 := by
    simp [unitVector]
  have hform : dot ((lam⁻¹ • velocity lam) - covariance.mulVec (unitVector first))
      (unitVector first) = lam⁻¹ * (η⁻¹ * lam) - 1 := by
    rw [EinsteinFull.dot_unitVector_right', hcov1, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      hvfirst, hone]
  show _ = dot ((lam⁻¹ • velocity lam) - covariance.mulVec (unitVector first))
      (unitVector first) / lam
  rw [hform, EinsteinFull.sharp_expansion_algebra lam η _ (avg lam) hlam'.ne' hηpos hη, ← hη]

end EinsteinFull.Blueprint
