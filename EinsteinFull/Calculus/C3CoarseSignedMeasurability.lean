import EinsteinFull.External.Source.AKMCoarsenedObjects
import EinsteinRelation.Correctors.HeatKernelConvolution
import EinsteinRelation.Environment.AKMMeasurableRepresentative
import EinsteinRelation.Environment.AKMReconstructionAgreement
import EinsteinRelation.Environment.EuclideanLipschitz
import EinsteinRelation.Correctors.BallMeanSquareScaling
import EinsteinRelation.Correctors.SpatialBallVolume
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Tactic
import EinsteinFull.Calculus.C1CoarseAnalyticUpperCuts
import EinsteinFull.Calculus.C1CoarseGaussianEnergyBounds
import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Frozen.HomogenizedGaussianKernel

open MeasureTheory Filter EinsteinRelation EinsteinRelation.External.AKM
open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinFull.External.Source.AKM
open scoped ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinFull ProbabilityTheory
attribute [local irreducible] coefficientRepresentative

/-- Signed measurability of the literal full-A₁ coarsened coefficient. -/
theorem coarseEntry_signed_aestronglyMeasurable (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (r : ℝ) (hr : D.dependenceRange ≤ r) (x : Vec d) (j k : Fin d) :
    AEStronglyMeasurable (fun a => EinsteinFull.External.Source.AKM.coarsenedCoefficient a
      (ellipticityScale D.ellipticity • homogenizedCoefficient Q)
      (D.dependenceRange⁻¹ • x) (r / D.dependenceRange) j k) (actualCoefficientLaw Q) := by
  classical
  clear hd hQ
  have hGaussian {d : ℕ} {K : ℝ} (hK : 0 ≤ K)
      (P : Measure (Coefficient d K)) [IsFiniteMeasure P]
      (z : Vec d) (r : ℝ) (hr : 0 < r) (p q : Vec d) :
      AEStronglyMeasurable (fun a => gaussianEnergyJ1 a z r p q) P := by
    -- Encode every coefficient by its actual local L² classes in a Polish product.
    have hencoding {d : ℕ} {K : ℝ} (hK : 0 ≤ K) :
        ∃ C : Coefficient d K → ∀ n : ℕ, Fin d → Fin d →
            Lp ℝ 2 (volume.restrict (Metric.closedBall (0 : Vec d) n)),
          PolishSpace (∀ n : ℕ, Fin d → Fin d →
            Lp ℝ 2 (volume.restrict (Metric.closedBall (0 : Vec d) n))) ∧
          @Measurable _ _ _ (borel _) C ∧
          ∀ a n i j, C a n i j =ᵐ[volume.restrict
            (Metric.closedBall (0 : Vec d) n)] (fun x => a x i j) := by
      as_aux_lemma =>
        have hentry (i j : Fin d) (S : Set (Vec d)) (hS : IsCompact S) :
            ∃ hL : ∀ a : Coefficient d K,
                MemLp (fun x => a.field x i j) 2 (volume.restrict S),
              @Measurable (Coefficient d K) (Lp ℝ 2 (volume.restrict S)) _ (borel _)
                (fun a => (hL a).toLp (fun x => a.field x i j)) := by
          have hlocal {Ω X : Type} [MeasurableSpace Ω] [MeasurableSpace X]
              (μ : Measure X) [SFinite μ] [IsSeparable μ]
              (f : Ω → X → ℝ) (hf : Measurable (fun s : Ω × X => f s.1 s.2))
              (hL : ∀ ω, MemLp (f ω) 2 μ) :
              @Measurable Ω (Lp ℝ 2 μ) _ (borel _) (fun ω => (hL ω).toLp (f ω)) := by
            let : MeasurableSpace (Lp ℝ 2 μ) := borel _
            let : BorelSpace (Lp ℝ 2 μ) := ⟨rfl⟩
            let : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
            let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
            have hcriterion (g : Ω → Lp ℝ 2 μ)
                (hg : ∀ y, Measurable (fun ω => dist (g ω) y)) : Measurable g := by
              apply measurable_of_isOpen
              intro s hs
              let I := {b : Lp ℝ 2 μ × ℝ // Metric.ball b.1 b.2 ⊆ s}
              have heq : (⋃ b : I, Metric.ball b.val.1 b.val.2) = s := by
                apply Set.Subset.antisymm
                · exact Set.iUnion_subset fun b => b.property
                · intro y hy
                  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hs y hy
                  exact Set.mem_iUnion.mpr ⟨⟨(y, ε), hsub⟩, Metric.mem_ball_self hε⟩
              obtain ⟨T, hT, hcover⟩ := TopologicalSpace.isOpen_iUnion_countable
                (fun b : I => Metric.ball b.val.1 b.val.2) (fun _ => Metric.isOpen_ball)
              rw [← heq, ← hcover, Set.preimage_iUnion₂]
              exact MeasurableSet.biUnion hT (fun b _ => measurableSet_lt (hg b.val.1) measurable_const)
            apply hcriterion
            intro u
            have hm : Measurable (fun s : Ω × X => f s.1 s.2 - u s.2) :=
              hf.sub ((Lp.stronglyMeasurable u).measurable.comp measurable_snd)
            have hnorm : Measurable (fun ω => eLpNorm (fun x => f ω x - u x) 2 μ) := by
              have hformula (ω : Ω) : eLpNorm (fun x => f ω x - u x) 2 μ =
                  (∫⁻ x, ‖f ω x - u x‖ₑ ^ (2 : ℝ≥0∞).toReal ∂μ) ^
                    (1 / (2 : ℝ≥0∞).toReal) :=
                eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
                  ((hL ω).aestronglyMeasurable.sub (Lp.aestronglyMeasurable u))
              simp_rw [hformula]
              exact ENNReal.continuous_rpow_const.measurable.comp
                ((ENNReal.continuous_rpow_const.measurable.comp hm.enorm).lintegral_prod_right')
            have heq : (fun ω => dist ((hL ω).toLp (f ω)) u) =
                (fun ω => (eLpNorm (fun x => f ω x - u x) 2 μ).toReal) := by
              funext ω
              rw [Lp.dist_def, eLpNorm_congr_ae ((hL ω).coeFn_toLp.sub Filter.EventuallyEq.rfl)]
              rfl
            rw [heq]
            exact hnorm.ennreal_toReal
          let μ := volume.restrict S
          let hL := fun a : Coefficient d K => coefficient_entry_memLp_on_compact hK a i j S hS
          have heq (a : Coefficient d K) :
              (fun x => coefficientRepresentative a x i j) =ᵐ[μ] (fun x => a.field x i j) := by
            filter_upwards [(coefficientRepresentative_ae_eq a).filter_mono
              (ae_restrict_le (μ := volume) (s := S))] with x hx
            exact congrFun (congrFun hx i) j
          have hR : Measurable (fun s : Coefficient d K × Vec d =>
              coefficientRepresentative s.1 s.2 i j) := by
            have hev : Continuous (fun A : Mat d => A i j) :=
              (continuous_apply j).comp (continuous_apply i)
            exact hev.measurable.comp (measurable_coefficientRepresentative (d := d) (K := K))
          have hLR (a : Coefficient d K) : MemLp (fun x => coefficientRepresentative a x i j) 2 μ :=
            (memLp_congr_ae (heq a)).mpr (hL a)
          refine ⟨hL, ?_⟩
          have hm := hlocal μ (fun a x => coefficientRepresentative a x i j) hR hLR
          have hclasses : (fun a => (hLR a).toLp (fun x => coefficientRepresentative a x i j)) =
              (fun a => (hL a).toLp (fun x => a.field x i j)) := by
            funext a
            exact MemLp.toLp_congr (hLR a) (hL a) (heq a)
          rw [hclasses] at hm
          exact hm
        let μ : ℕ → Measure (Vec d) := fun n =>
          volume.restrict (Metric.closedBall (0 : Vec d) n)
        let (n : ℕ) : MeasurableSpace (Lp ℝ 2 (μ n)) := borel _
        let (n : ℕ) : BorelSpace (Lp ℝ 2 (μ n)) := ⟨rfl⟩
        let : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
        let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
        let (n : ℕ) : IsSeparable (μ n) := by
          dsimp [μ]
          infer_instance
        let (n : ℕ) : SecondCountableTopology (Lp ℝ 2 (μ n)) := inferInstance
        choose hL hM using fun (n : ℕ) (i j : Fin d) =>
          hentry i j (Metric.closedBall (0 : Vec d) n) (isCompact_closedBall _ _)
        let C : Coefficient d K → ∀ n : ℕ, Fin d → Fin d → Lp ℝ 2 (μ n) :=
          fun a n i j => (hL n i j a).toLp (fun x => a.field x i j)
        refine ⟨C, ?_, ?_, ?_⟩
        · infer_instance
        · have hm : Measurable C := measurable_pi_iff.mpr (fun n =>
            measurable_pi_iff.mpr (fun i => measurable_pi_iff.mpr (fun j => hM n i j)))
          rw [← (Pi.borelSpace (X := fun n : ℕ => Fin d → Fin d →
            Lp ℝ 2 (μ n))).measurable_eq]
          exact hm
        · intro a n i j
          exact (hL n i j a).coeFn_toLp
    have hclasses {d : ℕ} {K : ℝ} {a : Coefficient d K}
        (w : SubquadraticHarmonic a) :
        ∃ U : ∀ n : ℕ, Lp ℝ 2 (volume.restrict (Metric.closedBall (0 : Vec d) n)),
        ∃ G : ∀ n : ℕ, Fin d → Lp ℝ 2 (volume.restrict (Metric.closedBall (0 : Vec d) n)),
          ∀ n, (U n =ᵐ[volume.restrict (Metric.closedBall (0 : Vec d) n)] w.potential) ∧
            ∀ i, G n i =ᵐ[volume.restrict (Metric.closedBall (0 : Vec d) n)]
              (fun x => w.grad x i) := by
      as_aux_lemma =>
        have hg (i : Fin d) : AEStronglyMeasurable (fun x => w.grad x i) volume := by
          simpa only [Measure.restrict_univ] using (w.weak_gradient i).2.1.aestronglyMeasurable
        have habs (v : Vec d) (i : Fin d) : |v i| ≤ euclideanNorm v := by
          have hsq : v i * v i ≤ ∑ j, v j * v j :=
            Finset.single_le_sum (f := fun j => v j * v j) (fun j _ => mul_self_nonneg (v j))
              (Finset.mem_univ i)
          unfold euclideanNorm euclideanSq dot
          apply Real.abs_le_sqrt
          simpa only [sq] using hsq
        let R (n : ℕ) : ℝ := ((d : ℝ) + 1) * ((n : ℝ) + 1)
        have hR (n : ℕ) : 0 < R n := by dsimp [R]; positivity
        have hle (n : ℕ) : volume.restrict (Metric.closedBall (0 : Vec d) n) ≤
            volume.restrict (ball (0 : Vec d) (R n)) := by
          apply Measure.restrict_mono_set volume
          intro y hy
          change euclideanNorm (y - 0) < R n
          rw [sub_zero]
          have hy' : ‖y‖ ≤ (n : ℝ) := by
            simpa only [Metric.mem_closedBall, dist_zero_right] using hy
          calc euclideanNorm y ≤ ((d : ℝ) + 1) * ‖y‖ := euclideanNorm_le_dimension_mul_norm y
            _ ≤ ((d : ℝ) + 1) * (n : ℝ) := mul_le_mul_of_nonneg_left hy' (by positivity)
            _ < R n := mul_lt_mul_of_pos_left (by linarith) (by positivity)
        have hu (n : ℕ) : MemLp w.potential 2
            (volume.restrict (Metric.closedBall (0 : Vec d) n)) :=
          MemLp.mono_measure (hle n) (w.local_energy (R n) (hR n)).1
        have hv (n : ℕ) (i : Fin d) : MemLp (fun x => w.grad x i) 2
            (volume.restrict (Metric.closedBall (0 : Vec d) n)) := by
          have hn : MemLp (fun x => euclideanNorm (w.grad x)) 2
              (volume.restrict (Metric.closedBall (0 : Vec d) n)) :=
            MemLp.mono_measure (hle n) (w.local_energy (R n) (hR n)).2
          apply hn.of_le ((hg i).restrict)
          exact Filter.Eventually.of_forall (fun x => by
            change |w.grad x i| ≤ |euclideanNorm (w.grad x)|
            exact (habs (w.grad x) i).trans (le_abs_self _))
        exact ⟨fun n => (hu n).toLp w.potential,
          fun n i => (hv n i).toLp (fun x => w.grad x i),
          fun n => ⟨(hu n).coeFn_toLp, fun i => (hv n i).coeFn_toLp⟩⟩
    have hcuts {E F : Type} [TopologicalSpace E] [PolishSpace E]
        [MeasurableSpace E] [BorelSpace E] [TopologicalSpace F] [PolishSpace F]
        [MeasurableSpace F] [BorelSpace F] (G : Set (E × F)) (hG : MeasurableSet G)
        (J : E × F → ℝ) (hJ : Measurable J) (w₀ : F) (h₀ : ∀ a, (a, w₀) ∈ G)
        (B : ℝ) :
        let V := fun a => sSup {e : ℝ | ∃ w : F, (a, w) ∈ G ∧
          e = min B (max 0 (J (a, w)))}
        ∀ t : ℝ, AnalyticSet {a : E | t < V a} := by
      as_aux_lemma =>
        classical
        dsimp only
        intro t
        let H : E × F → ℝ := fun s => min B (max 0 (J s))
        have hH : Measurable H := measurable_const.min (measurable_const.max hJ)
        have heq : {a : E | t < sSup {e : ℝ | ∃ w : F, (a, w) ∈ G ∧ e = H (a, w)}} =
            Prod.fst '' (G ∩ {s | t < H s}) := by
          ext a
          have hb : BddAbove {e : ℝ | ∃ w : F, (a, w) ∈ G ∧ e = H (a, w)} := by
            refine ⟨B, ?_⟩
            rintro e ⟨w, hw, rfl⟩
            exact min_le_left _ _
          have hn : Set.Nonempty {e : ℝ | ∃ w : F, (a, w) ∈ G ∧ e = H (a, w)} :=
            ⟨_, w₀, h₀ a, rfl⟩
          simp only [Set.mem_ofPred_eq]
          rw [lt_csSup_iff hb hn]
          constructor
          · rintro ⟨e, ⟨w, hw, rfl⟩, ht⟩
            exact ⟨(a, w), ⟨hw, ht⟩, rfl⟩
          · rintro ⟨⟨b, w⟩, ⟨hw, ht⟩, he⟩
            change b = a at he
            subst b
            exact ⟨_, ⟨w, hw, rfl⟩, ht⟩
        change AnalyticSet {a : E | t < sSup {e : ℝ | ∃ w : F,
          (a, w) ∈ G ∧ e = H (a, w)}}
        rw [heq]
        exact (hG.inter (measurableSet_lt measurable_const hH)).analyticSet_image measurable_fst
    -- All compact test equations, compatibility, and source growth form a Borel graph.
    have hgraph (d : ℕ) :
        let μ := fun n : ℕ => volume.restrict (Metric.closedBall (0 : Vec d) (n : ℝ))
        let E := ∀ n : ℕ, Fin d → Fin d → Lp ℝ 2 (μ n)
        let F := ∀ n : ℕ, Lp ℝ 2 (μ n) × (Fin d → Lp ℝ 2 (μ n))
        let : MeasurableSpace E := borel E
        let : MeasurableSpace F := borel F
        let G := {s : E × F |
          (∀ (n : ℕ) (φ : Vec d → ℝ), IsSpatialTest Set.univ φ →
            tsupport φ ⊆ Metric.closedBall (0 : Vec d) n →
            (∀ i : Fin d,
              (∫ x in Metric.closedBall (0 : Vec d) n, (s.2 n).1 x * coordinateDerivative i φ x) =
                -(∫ x in Metric.closedBall (0 : Vec d) n, (s.2 n).2 i x * φ x)) ∧
            (∑ i, ∑ j, ∫ x in Metric.closedBall (0 : Vec d) n,
              coordinateDerivative i φ x * s.1 n i j x * (s.2 n).2 j x) = 0) ∧
          (∀ n m : ℕ, ((s.2 n).1 : Vec d → ℝ) =ᵐ[volume.restrict
            (Metric.closedBall (0 : Vec d) n ∩ Metric.closedBall (0 : Vec d) m)] (s.2 m).1) ∧
          (∀ (n m : ℕ) (i : Fin d), ((s.2 n).2 i : Vec d → ℝ) =ᵐ[volume.restrict
            (Metric.closedBall (0 : Vec d) n ∩ Metric.closedBall (0 : Vec d) m)] (s.2 m).2 i) ∧
          Tendsto (fun n : ℕ => ‖(s.2 n).1‖ ^ 2 / (n : ℝ) ^ (d + 4)) atTop (𝓝 0)}
        MeasurableSet G ∧ ∀ A : E, (A, fun _ => (0, fun _ => 0)) ∈ G := by
      as_aux_lemma =>
        classical
        have hequations (d : ℕ) :
            let μ := fun n : ℕ => volume.restrict (Metric.closedBall (0 : Vec d) (n : ℝ))
            let E := ∀ n : ℕ, Fin d → Fin d → Lp ℝ 2 (μ n)
            let F := ∀ n : ℕ, Lp ℝ 2 (μ n) × (Fin d → Lp ℝ 2 (μ n))
            IsClosed {s : E × F | ∀ (n : ℕ) (φ : Vec d → ℝ),
              IsSpatialTest Set.univ φ → tsupport φ ⊆ Metric.closedBall (0 : Vec d) n →
              (∀ i : Fin d,
                (∫ x in Metric.closedBall (0 : Vec d) n, (s.2 n).1 x * coordinateDerivative i φ x) =
                  -(∫ x in Metric.closedBall (0 : Vec d) n, (s.2 n).2 i x * φ x)) ∧
              (∑ i, ∑ j, ∫ x in Metric.closedBall (0 : Vec d) n,
                coordinateDerivative i φ x * s.1 n i j x * (s.2 n).2 j x) = 0} := by
          classical
          have hclosed {X : Type} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
              {d : ℕ} {T : Type} (ψ : T → Fin d → X → ℝ) (η : T → X → ℝ)
              (hψ : ∀ t i, AEStronglyMeasurable (ψ t i) μ)
              (hη : ∀ t, AEStronglyMeasurable (η t) μ)
              (C : T → Fin d → NNReal) (B : T → NNReal)
              (hC : ∀ t i, ∀ᵐ x ∂μ, ‖ψ t i x‖ ≤ C t i)
              (hB : ∀ t, ∀ᵐ x ∂μ, ‖η t x‖ ≤ B t) :
              IsClosed {s : (Fin d → Fin d → Lp ℝ 2 μ) × (Lp ℝ 2 μ × (Fin d → Lp ℝ 2 μ)) |
                (∀ t i, (∫ x, s.2.1 x * ψ t i x ∂μ) = -(∫ x, s.2.2 i x * η t x ∂μ)) ∧
                (∀ t, (∑ i, ∑ j, ∫ x, ψ t i x * s.1 i j x * s.2.2 j x ∂μ) = 0)} := by
            have hpair (ψ : X → ℝ) (hψ : AEStronglyMeasurable ψ μ) (C : NNReal)
                (hC : ∀ᵐ x ∂μ, ‖ψ x‖ ≤ C) :
                Continuous (fun s : Lp ℝ 2 μ × Lp ℝ 2 μ => ∫ x, ψ x * s.1 x * s.2 x ∂μ) := by
              let : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
              let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
              have hm (f : Lp ℝ 2 μ) : MemLp (fun x => ψ x * f x) 2 μ := by
                apply (Lp.memLp f).of_le_mul (c := (C : ℝ)) (hψ.mul (Lp.aestronglyMeasurable f))
                filter_upwards [hC] with x hx
                simpa only [Pi.mul_apply, norm_mul] using mul_le_mul_of_nonneg_right hx (norm_nonneg (f x))
              let M (f : Lp ℝ 2 μ) : Lp ℝ 2 μ := (hm f).toLp (fun x => ψ x * f x)
              have hM (f : Lp ℝ 2 μ) : M f =ᵐ[μ] fun x => ψ x * f x := (hm f).coeFn_toLp
              have hLip : LipschitzWith C M := by
                apply LipschitzWith.of_dist_le_mul
                intro f g
                rw [dist_eq_norm, dist_eq_norm]
                apply Lp.norm_le_mul_norm_of_ae_le_mul
                filter_upwards [Lp.coeFn_sub (M f) (M g), hM f, hM g, Lp.coeFn_sub f g, hC]
                  with x hsub hf hg hfg hx
                rw [hsub, hfg]
                change ‖M f x - M g x‖ ≤ (C : ℝ) * ‖f x - g x‖
                rw [hf, hg, ← mul_sub, norm_mul]
                exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
              have heq (s : Lp ℝ 2 μ × Lp ℝ 2 μ) :
                  (∫ x, ψ x * s.1 x * s.2 x ∂μ) = inner ℝ (M s.1) s.2 := by
                rw [L2.inner_def]
                apply integral_congr_ae
                filter_upwards [hM s.1] with x hx
                simp [hx, mul_comm]
              simp_rw [heq]
              exact (hLip.continuous.comp continuous_fst).inner continuous_snd
            have hlinear (θ : X → ℝ) (hθ : MemLp θ 2 μ) :
                Continuous (fun f : Lp ℝ 2 μ => ∫ x, f x * θ x ∂μ) := by
              have heq (f : Lp ℝ 2 μ) : (∫ x, f x * θ x ∂μ) = inner ℝ f (hθ.toLp θ) := by
                rw [L2.inner_def]
                apply integral_congr_ae
                filter_upwards [hθ.coeFn_toLp] with x hx
                simp [hx, mul_comm]
              simp_rw [heq]
              exact continuous_id.inner continuous_const
            have hgrad : IsClosed {s : (Fin d → Fin d → Lp ℝ 2 μ) ×
                (Lp ℝ 2 μ × (Fin d → Lp ℝ 2 μ)) |
                ∀ t i, (∫ x, s.2.1 x * ψ t i x ∂μ) = -(∫ x, s.2.2 i x * η t x ∂μ)} := by
              simp only [Set.ofPred_forall]
              apply isClosed_iInter
              intro t
              apply isClosed_iInter
              intro i
              exact isClosed_eq
                ((hlinear (ψ t i) (MemLp.of_bound (hψ t i) (C t i) (hC t i))).comp (by fun_prop))
                (((hlinear (η t) (MemLp.of_bound (hη t) (B t) (hB t))).comp (by fun_prop)).neg)
            have hflux : IsClosed {s : (Fin d → Fin d → Lp ℝ 2 μ) ×
                (Lp ℝ 2 μ × (Fin d → Lp ℝ 2 μ)) |
                ∀ t, (∑ i, ∑ j, ∫ x, ψ t i x * s.1 i j x * s.2.2 j x ∂μ) = 0} := by
              simp only [Set.ofPred_forall]
              apply isClosed_iInter
              intro t
              have hc : Continuous (fun s : (Fin d → Fin d → Lp ℝ 2 μ) ×
                  (Lp ℝ 2 μ × (Fin d → Lp ℝ 2 μ)) =>
                  ∑ i, ∑ j, ∫ x, ψ t i x * s.1 i j x * s.2.2 j x ∂μ) := by
                refine continuous_finsetSum _ ?_
                intro i _
                refine continuous_finsetSum _ ?_
                intro j _
                have hp : Continuous (fun s : (Fin d → Fin d → Lp ℝ 2 μ) ×
                    (Lp ℝ 2 μ × (Fin d → Lp ℝ 2 μ)) => (s.1 i j, s.2.2 j)) := by fun_prop
                simpa only [Function.comp_def] using
                  (hpair (ψ t i) (hψ t i) (C t i) (hC t i)).comp hp
              exact isClosed_eq hc continuous_const
            exact hgrad.inter hflux
          have hbounded {d : ℕ} (φ : Vec d → ℝ) (hφ : IsSpatialTest Set.univ φ) :
              (Measurable φ ∧ ∃ C : NNReal, ∀ x, ‖φ x‖ ≤ C) ∧
              ∀ i : Fin d, Measurable (coordinateDerivative i φ) ∧
                ∃ C : NNReal, ∀ x, ‖coordinateDerivative i φ x‖ ≤ C := by
            have hb (f : Vec d → ℝ) (hc : Continuous f) (hs : HasCompactSupport f) :
                ∃ C : NNReal, ∀ x, ‖f x‖ ≤ C := by
              obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
              exact ⟨⟨max C 0, le_max_right _ _⟩, fun x => (hC x).trans (le_max_left _ _)⟩
            refine ⟨⟨hφ.1.continuous.measurable, hb φ hφ.1.continuous hφ.2.1⟩, ?_⟩
            intro i
            have hc : Continuous (coordinateDerivative i φ) := by
              exact (hφ.1.continuous_fderiv_apply (by simp)).comp
                (continuous_id.prodMk (continuous_const : Continuous (fun _ : Vec d => unitVector i)))
            have hs : HasCompactSupport (coordinateDerivative i φ) :=
              hφ.2.1.fderiv_apply ℝ (unitVector i)
            exact ⟨hc.measurable, hb _ hc hs⟩

          let μ := fun n : ℕ => volume.restrict (Metric.closedBall (0 : Vec d) (n : ℝ))
          let E := ∀ n : ℕ, Fin d → Fin d → Lp ℝ 2 (μ n)
          let F := ∀ n : ℕ, Lp ℝ 2 (μ n) × (Fin d → Lp ℝ 2 (μ n))
          let T (n : ℕ) := {φ : Vec d → ℝ // IsSpatialTest Set.univ φ ∧
            tsupport φ ⊆ Metric.closedBall (0 : Vec d) n}
          have hn (n : ℕ) : IsClosed {s : E × F | ∀ t : T n,
              (∀ i : Fin d, (∫ x in Metric.closedBall (0 : Vec d) n, (s.2 n).1 x * coordinateDerivative i t.1 x) =
                -(∫ x in Metric.closedBall (0 : Vec d) n, (s.2 n).2 i x * t.1 x)) ∧
              (∑ i, ∑ j, ∫ x in Metric.closedBall (0 : Vec d) n,
                coordinateDerivative i t.1 x * s.1 n i j x * (s.2 n).2 j x) = 0} := by
            let : IsFiniteMeasure (μ n) := isFiniteMeasure_restrict.mpr
              (isCompact_closedBall (0 : Vec d) (n : ℝ)).measure_ne_top
            let ψ (t : T n) (i : Fin d) := coordinateDerivative i t.1
            let η (t : T n) := t.1
            have hψ (t : T n) (i : Fin d) : Measurable (ψ t i) :=
              ((hbounded t.1 t.2.1).2 i).1
            have hη (t : T n) : Measurable (η t) := (hbounded t.1 t.2.1).1.1
            let C (t : T n) (i : Fin d) : NNReal :=
              Classical.choose ((hbounded t.1 t.2.1).2 i).2
            let B (t : T n) : NNReal := Classical.choose (hbounded t.1 t.2.1).1.2
            have hC (t : T n) (i : Fin d) : ∀ᵐ x ∂μ n, ‖ψ t i x‖ ≤ C t i :=
              Filter.Eventually.of_forall (Classical.choose_spec ((hbounded t.1 t.2.1).2 i).2)
            have hB (t : T n) : ∀ᵐ x ∂μ n, ‖η t x‖ ≤ B t :=
              Filter.Eventually.of_forall (Classical.choose_spec (hbounded t.1 t.2.1).1.2)
            have hc := hclosed (X := Vec d) (d := d) (T := T n) (μ n) ψ η (fun t i => (hψ t i).aestronglyMeasurable)
              (fun t => (hη t).aestronglyMeasurable) C B hC hB
            have hp : Continuous (fun s : E × F => (s.1 n, s.2 n)) := by fun_prop
            have heq : {s : E × F | ∀ t : T n,
                (∀ i : Fin d, (∫ x in Metric.closedBall (0 : Vec d) n, (s.2 n).1 x * coordinateDerivative i t.1 x) =
                  -(∫ x in Metric.closedBall (0 : Vec d) n, (s.2 n).2 i x * t.1 x)) ∧
                (∑ i, ∑ j, ∫ x in Metric.closedBall (0 : Vec d) n,
                  coordinateDerivative i t.1 x * s.1 n i j x * (s.2 n).2 j x) = 0} =
                (fun s : E × F => (s.1 n, s.2 n)) ⁻¹'
                  {s | (∀ t : T n, ∀ i : Fin d, (∫ x in Metric.closedBall (0 : Vec d) n, s.2.1 x * ψ t i x) =
                      -(∫ x in Metric.closedBall (0 : Vec d) n, s.2.2 i x * η t x)) ∧
                    (∀ t : T n, (∑ i, ∑ j, ∫ x in Metric.closedBall (0 : Vec d) n, ψ t i x * s.1 i j x * s.2.2 j x) = 0)} := by
              ext s
              simp only [Set.mem_ofPred_eq, Set.mem_preimage]
              exact forall_and
            rw [heq]
            exact hc.preimage hp
          have hall : IsClosed {s : E × F | ∀ n : ℕ, ∀ t : T n,
              (∀ i : Fin d, (∫ x in Metric.closedBall (0 : Vec d) n, (s.2 n).1 x * coordinateDerivative i t.1 x) =
                -(∫ x in Metric.closedBall (0 : Vec d) n, (s.2 n).2 i x * t.1 x)) ∧
              (∑ i, ∑ j, ∫ x in Metric.closedBall (0 : Vec d) n,
                coordinateDerivative i t.1 x * s.1 n i j x * (s.2 n).2 j x) = 0} := by
            simpa only [Set.ofPred_forall] using isClosed_iInter hn
          convert hall using 1
          ext s
          constructor
          · intro h n t
            exact h n t.1 t.2.1 t.2.2
          · intro h n φ hφ hs
            exact h n ⟨φ, hφ, hs⟩

        have hconstraints (d : ℕ) :
            let μ := fun n : ℕ => volume.restrict (Metric.closedBall (0 : Vec d) (n : ℝ))
            let F := ∀ n : ℕ, Lp ℝ 2 (μ n) × (Fin d → Lp ℝ 2 (μ n))
            let : MeasurableSpace F := borel F
            MeasurableSet {v : F |
              (∀ n m : ℕ, ((v n).1 : Vec d → ℝ) =ᵐ[volume.restrict
                (Metric.closedBall (0 : Vec d) n ∩ Metric.closedBall (0 : Vec d) m)] (v m).1) ∧
              (∀ (n m : ℕ) (i : Fin d), ((v n).2 i : Vec d → ℝ) =ᵐ[volume.restrict
                (Metric.closedBall (0 : Vec d) n ∩ Metric.closedBall (0 : Vec d) m)] (v m).2 i) ∧
              Tendsto (fun n : ℕ => ‖(v n).1‖ ^ 2 / (n : ℝ) ^ (d + 4)) atTop (𝓝 0)} := by
          classical
          have hcompat {X : Type} [MeasurableSpace X] (μ : Measure X) (S : ℕ → Set X)
              (hS : ∀ n, MeasurableSet (S n)) (hcover : ∀ x, ∃ n, x ∈ S n) :
              IsClosed {u : ∀ n : ℕ, Lp ℝ 2 (μ.restrict (S n)) |
                ∀ n m, (u n : X → ℝ) =ᵐ[μ.restrict (S n ∩ S m)] u m} ∧
              ∀ u : ∀ n : ℕ, Lp ℝ 2 (μ.restrict (S n)),
                (∀ n m, (u n : X → ℝ) =ᵐ[μ.restrict (S n ∩ S m)] u m) →
                ∃ f : X → ℝ, Measurable f ∧ ∀ n, f =ᵐ[μ.restrict (S n)] u n := by
            classical
            let : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
            let ρ (n m : ℕ) := μ.restrict (S n ∩ S m)
            have hleft (n m : ℕ) : ρ n m ≤ (1 : ℝ≥0∞) • μ.restrict (S n) := by
              simpa only [one_smul] using Measure.restrict_mono_set μ Set.inter_subset_left
            have hright (n m : ℕ) : ρ n m ≤ (1 : ℝ≥0∞) • μ.restrict (S m) := by
              simpa only [one_smul] using Measure.restrict_mono_set μ Set.inter_subset_right
            let L (n m : ℕ) : Lp ℝ 2 (μ.restrict (S n)) →L[ℝ] Lp ℝ 2 (ρ n m) :=
              Lp.LpToLpOfMeasureLeSMul (by norm_num : (1 : ℝ≥0∞) ≠ ∞) (hleft n m)
            let R (n m : ℕ) : Lp ℝ 2 (μ.restrict (S m)) →L[ℝ] Lp ℝ 2 (ρ n m) :=
              Lp.LpToLpOfMeasureLeSMul (by norm_num : (1 : ℝ≥0∞) ≠ ∞) (hright n m)
            have hL (n m : ℕ) (v : Lp ℝ 2 (μ.restrict (S n))) : L n m v =ᵐ[ρ n m] v :=
              Lp.coeFn_LpToLpOfMeasureLeSMul (by norm_num : (1 : ℝ≥0∞) ≠ ∞) (hleft n m) v
            have hR (n m : ℕ) (v : Lp ℝ 2 (μ.restrict (S m))) : R n m v =ᵐ[ρ n m] v :=
              Lp.coeFn_LpToLpOfMeasureLeSMul (by norm_num : (1 : ℝ≥0∞) ≠ ∞) (hright n m) v
            have heq (n m : ℕ) (u : ∀ n : ℕ, Lp ℝ 2 (μ.restrict (S n))) :
                L n m (u n) = R n m (u m) ↔ (u n : X → ℝ) =ᵐ[ρ n m] u m := by
              constructor
              · intro h
                have hl := hL n m (u n)
                rw [h] at hl
                exact hl.symm.trans (hR n m (u m))
              · intro h
                exact Lp.ext ((hL n m (u n)).trans (h.trans (hR n m (u m)).symm))
            constructor
            · have hc : IsClosed {u : ∀ n : ℕ, Lp ℝ 2 (μ.restrict (S n)) |
                  ∀ n m, L n m (u n) = R n m (u m)} := by
                simp only [Set.ofPred_forall]
                exact isClosed_iInter fun n => isClosed_iInter fun m =>
                  isClosed_eq ((L n m).continuous.comp (continuous_apply n))
                    ((R n m).continuous.comp (continuous_apply m))
              simpa only [heq] using hc
            · intro u hu
              let i (x : X) := Nat.find (hcover x)
              have hi : Measurable i := measurable_find hcover hS
              let f (x : X) := u (i x) x
              refine ⟨f, ?_, ?_⟩
              · have hrep : Measurable (fun s : ℕ × X => u s.1 s.2) :=
                  measurable_from_prod_countable_right (fun n => (Lp.stronglyMeasurable (u n)).measurable)
                exact hrep.comp (hi.prodMk measurable_id)
              · intro n
                have hnm (m : ℕ) : ∀ᵐ x ∂μ.restrict (S n), x ∈ S m → u n x = u m x := by
                  apply (ae_restrict_iff' (hS m)).mp
                  rw [Measure.restrict_restrict (hS m), Set.inter_comm (S m) (S n)]
                  exact hu n m
                filter_upwards [ae_all_iff.mpr hnm] with x hx
                exact (hx (i x) (Nat.find_spec (hcover x))).symm

          let S := fun n : ℕ => Metric.closedBall (0 : Vec d) (n : ℝ)
          let μ := fun n : ℕ => volume.restrict (S n)
          let F := ∀ n : ℕ, Lp ℝ 2 (μ n) × (Fin d → Lp ℝ 2 (μ n))
          let : MeasurableSpace F := borel F
          let : BorelSpace F := ⟨rfl⟩
          have hcover (x : Vec d) : ∃ n : ℕ, x ∈ S n := by
            obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
            exact ⟨n, by simpa only [S, Metric.mem_closedBall, dist_zero_right] using hn.le⟩
          have hc := (hcompat volume S (fun n => measurableSet_closedBall) hcover).1
          have hp : Continuous (fun v : F => fun n : ℕ => (v n).1) := by fun_prop
          have hpotential : IsClosed {v : F | ∀ n m : ℕ,
              ((v n).1 : Vec d → ℝ) =ᵐ[volume.restrict (S n ∩ S m)] (v m).1} :=
            hc.preimage hp
          have hg (i : Fin d) : Continuous (fun v : F => fun n : ℕ => (v n).2 i) := by fun_prop
          have hgradient : IsClosed {v : F | ∀ (n m : ℕ) (i : Fin d),
              ((v n).2 i : Vec d → ℝ) =ᵐ[volume.restrict (S n ∩ S m)] (v m).2 i} := by
            have hh : IsClosed {v : F | ∀ (i : Fin d) (n m : ℕ),
                ((v n).2 i : Vec d → ℝ) =ᵐ[volume.restrict (S n ∩ S m)] (v m).2 i} := by
              have hi (i : Fin d) : IsClosed {v : F | ∀ n m : ℕ,
                  ((v n).2 i : Vec d → ℝ) =ᵐ[volume.restrict (S n ∩ S m)] (v m).2 i} :=
                hc.preimage (hg i)
              simpa only [Set.ofPred_forall] using isClosed_iInter hi
            convert hh using 1
            ext v
            simp only [Set.mem_ofPred_eq]
            exact ⟨fun h i n m => h n m i, fun h n m i => h i n m⟩
          have hgrowth : MeasurableSet {v : F |
              Tendsto (fun n : ℕ => ‖(v n).1‖ ^ 2 / (n : ℝ) ^ (d + 4)) atTop (𝓝 0)} := by
            apply measurableSet_tendsto_fun (g := fun _ => (0 : ℝ))
            · intro n
              have hn : Continuous (fun v : F => ‖(v n).1‖ ^ 2 / (n : ℝ) ^ (d + 4)) := by fun_prop
              exact hn.measurable
            · exact measurable_const
          exact hpotential.measurableSet.inter (hgradient.measurableSet.inter hgrowth)

        let μ := fun n : ℕ => volume.restrict (Metric.closedBall (0 : Vec d) (n : ℝ))
        let E := ∀ n : ℕ, Fin d → Fin d → Lp ℝ 2 (μ n)
        let F := ∀ n : ℕ, Lp ℝ 2 (μ n) × (Fin d → Lp ℝ 2 (μ n))
        let : MeasurableSpace E := borel E
        let : MeasurableSpace F := borel F
        let : BorelSpace E := ⟨rfl⟩
        let : BorelSpace F := ⟨rfl⟩
        let : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
        let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
        let (n : ℕ) : IsSeparable (μ n) := by dsimp [μ]; infer_instance
        let (n : ℕ) : SecondCountableTopology (Lp ℝ 2 (μ n)) := inferInstance
        let : SecondCountableTopology E := inferInstance
        let : SecondCountableTopology F := inferInstance
        have hz (n : ℕ) : (0 : Lp ℝ 2 (μ n)) =ᵐ[μ n] (fun _ => (0 : ℝ)) :=
          Lp.coeFn_zero ℝ 2 (μ n)
        have hzc (n m : ℕ) : (0 : Lp ℝ 2 (μ n)) =ᵐ[volume.restrict
            (Metric.closedBall (0 : Vec d) n ∩ Metric.closedBall (0 : Vec d) m)]
            (0 : Lp ℝ 2 (μ m)) := by
          exact ((hz n).filter_mono (ae_mono (Measure.restrict_mono_set volume
            Set.inter_subset_left))).trans ((hz m).filter_mono
            (ae_mono (Measure.restrict_mono_set volume Set.inter_subset_right))).symm
        constructor
        · exact (hequations d).measurableSet.inter ((hconstraints d).preimage measurable_snd)
        · intro A
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro n φ hφ hs
            constructor
            · intro i
              have he (θ : Vec d → ℝ) :
                  (∫ x in Metric.closedBall (0 : Vec d) n, (0 : Lp ℝ 2 (μ n)) x * θ x) = 0 := by
                calc
                  _ = ∫ _x in Metric.closedBall (0 : Vec d) n, (0 : ℝ) := by
                    apply integral_congr_ae
                    filter_upwards [hz n] with x hx
                    simp only [hx, zero_mul]
                  _ = 0 := integral_zero _ _
              rw [he, he, neg_zero]
            · have he (i j : Fin d) : (∫ x in Metric.closedBall (0 : Vec d) n,
                  coordinateDerivative i φ x * A n i j x * (0 : Lp ℝ 2 (μ n)) x) = 0 := by
                calc
                  _ = ∫ _x in Metric.closedBall (0 : Vec d) n, (0 : ℝ) := by
                    apply integral_congr_ae
                    filter_upwards [hz n] with x hx
                    simp only [hx, mul_zero]
                  _ = 0 := integral_zero _ _
              simp only [he, Finset.sum_const_zero]
          · intro n m
            exact hzc n m
          · intro n m i
            exact hzc n m
          · simpa only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
              zero_div] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    -- Each actual coefficient fiber is exactly the full source A₁ class.
    have hfiber {d : ℕ} {K : ℝ} (hK : 0 ≤ K) (a : Coefficient d K)
        (A : ∀ n : ℕ, Fin d → Fin d →
          Lp ℝ 2 (volume.restrict (Metric.closedBall (0 : Vec d) n)))
        (hA : ∀ (n : ℕ) (i j : Fin d), A n i j =ᵐ[volume.restrict
          (Metric.closedBall (0 : Vec d) n)] (fun x => a x i j))
        (U : ∀ n : ℕ, Lp ℝ 2 (volume.restrict (Metric.closedBall (0 : Vec d) n)))
        (G : ∀ n : ℕ, Fin d → Lp ℝ 2 (volume.restrict (Metric.closedBall (0 : Vec d) n))) :
        ((∀ (n : ℕ) (φ : Vec d → ℝ), IsSpatialTest Set.univ φ →
          tsupport φ ⊆ Metric.closedBall (0 : Vec d) n →
          (∀ i : Fin d,
            (∫ x in Metric.closedBall (0 : Vec d) n, U n x * coordinateDerivative i φ x) =
              -(∫ x in Metric.closedBall (0 : Vec d) n, G n i x * φ x)) ∧
          (∑ i, ∑ j, ∫ x in Metric.closedBall (0 : Vec d) n,
            coordinateDerivative i φ x * A n i j x * G n j x) = 0) ∧
        (∀ n m : ℕ, (U n : Vec d → ℝ) =ᵐ[volume.restrict
          (Metric.closedBall (0 : Vec d) n ∩ Metric.closedBall (0 : Vec d) m)] U m) ∧
        (∀ (n m : ℕ) (i : Fin d), (G n i : Vec d → ℝ) =ᵐ[volume.restrict
          (Metric.closedBall (0 : Vec d) n ∩ Metric.closedBall (0 : Vec d) m)] G m i) ∧
        Tendsto (fun n : ℕ => ‖U n‖ ^ 2 / (n : ℝ) ^ (d + 4)) atTop (𝓝 0)) ↔
        ∃ w : SubquadraticHarmonic a, ∀ n : ℕ,
          (U n =ᵐ[volume.restrict (Metric.closedBall (0 : Vec d) n)] w.potential) ∧
          ∀ i : Fin d, G n i =ᵐ[volume.restrict (Metric.closedBall (0 : Vec d) n)]
            (fun x => w.grad x i) := by
      as_aux_lemma =>
        classical
        have hglue {X : Type} [MeasurableSpace X] (μ : Measure X) (S : ℕ → Set X)
            (hS : ∀ n, MeasurableSet (S n)) (hcover : ∀ x, ∃ n, x ∈ S n) :
            IsClosed {u : ∀ n : ℕ, Lp ℝ 2 (μ.restrict (S n)) |
              ∀ n m, (u n : X → ℝ) =ᵐ[μ.restrict (S n ∩ S m)] u m} ∧
            ∀ u : ∀ n : ℕ, Lp ℝ 2 (μ.restrict (S n)),
              (∀ n m, (u n : X → ℝ) =ᵐ[μ.restrict (S n ∩ S m)] u m) →
              ∃ f : X → ℝ, Measurable f ∧ ∀ n, f =ᵐ[μ.restrict (S n)] u n := by
          classical
          let : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
          let ρ (n m : ℕ) := μ.restrict (S n ∩ S m)
          have hleft (n m : ℕ) : ρ n m ≤ (1 : ℝ≥0∞) • μ.restrict (S n) := by
            simpa only [one_smul] using Measure.restrict_mono_set μ Set.inter_subset_left
          have hright (n m : ℕ) : ρ n m ≤ (1 : ℝ≥0∞) • μ.restrict (S m) := by
            simpa only [one_smul] using Measure.restrict_mono_set μ Set.inter_subset_right
          let L (n m : ℕ) : Lp ℝ 2 (μ.restrict (S n)) →L[ℝ] Lp ℝ 2 (ρ n m) :=
            Lp.LpToLpOfMeasureLeSMul (by norm_num : (1 : ℝ≥0∞) ≠ ∞) (hleft n m)
          let R (n m : ℕ) : Lp ℝ 2 (μ.restrict (S m)) →L[ℝ] Lp ℝ 2 (ρ n m) :=
            Lp.LpToLpOfMeasureLeSMul (by norm_num : (1 : ℝ≥0∞) ≠ ∞) (hright n m)
          have hL (n m : ℕ) (v : Lp ℝ 2 (μ.restrict (S n))) : L n m v =ᵐ[ρ n m] v :=
            Lp.coeFn_LpToLpOfMeasureLeSMul (by norm_num : (1 : ℝ≥0∞) ≠ ∞) (hleft n m) v
          have hR (n m : ℕ) (v : Lp ℝ 2 (μ.restrict (S m))) : R n m v =ᵐ[ρ n m] v :=
            Lp.coeFn_LpToLpOfMeasureLeSMul (by norm_num : (1 : ℝ≥0∞) ≠ ∞) (hright n m) v
          have heq (n m : ℕ) (u : ∀ n : ℕ, Lp ℝ 2 (μ.restrict (S n))) :
              L n m (u n) = R n m (u m) ↔ (u n : X → ℝ) =ᵐ[ρ n m] u m := by
            constructor
            · intro h
              have hl := hL n m (u n)
              rw [h] at hl
              exact hl.symm.trans (hR n m (u m))
            · intro h
              exact Lp.ext ((hL n m (u n)).trans (h.trans (hR n m (u m)).symm))
          constructor
          · have hc : IsClosed {u : ∀ n : ℕ, Lp ℝ 2 (μ.restrict (S n)) |
                ∀ n m, L n m (u n) = R n m (u m)} := by
              simp only [Set.ofPred_forall]
              exact isClosed_iInter fun n => isClosed_iInter fun m =>
                isClosed_eq ((L n m).continuous.comp (continuous_apply n))
                  ((R n m).continuous.comp (continuous_apply m))
            simpa only [heq] using hc
          · intro u hu
            let i (x : X) := Nat.find (hcover x)
            have hi : Measurable i := measurable_find hcover hS
            let f (x : X) := u (i x) x
            refine ⟨f, ?_, ?_⟩
            · have hrep : Measurable (fun s : ℕ × X => u s.1 s.2) :=
                measurable_from_prod_countable_right (fun n => (Lp.stronglyMeasurable (u n)).measurable)
              exact hrep.comp (hi.prodMk measurable_id)
            · intro n
              have hnm (m : ℕ) : ∀ᵐ x ∂μ.restrict (S n), x ∈ S m → u n x = u m x := by
                apply (ae_restrict_iff' (hS m)).mp
                rw [Measure.restrict_restrict (hS m), Set.inter_comm (S m) (S n)]
                exact hu n m
              filter_upwards [ae_all_iff.mpr hnm] with x hx
              exact (hx (i x) (Nat.find_spec (hcover x))).symm
        have hweak {d : ℕ} (f : Vec d → ℝ) (g : Vec d → Vec d)
            (hf : ∀ n : ℕ, MemLp f 2 (volume.restrict (Metric.closedBall (0 : Vec d) n)))
            (hg : ∀ (n : ℕ) (i : Fin d),
              MemLp (fun x => g x i) 2 (volume.restrict (Metric.closedBall (0 : Vec d) n))) :
            HasWeakGradient Set.univ f g ↔
              ∀ (n : ℕ) (φ : Vec d → ℝ), IsSpatialTest Set.univ φ →
                tsupport φ ⊆ Metric.closedBall (0 : Vec d) n → ∀ i : Fin d,
                  (∫ x in Metric.closedBall (0 : Vec d) n, f x * coordinateDerivative i φ x) =
                    -(∫ x in Metric.closedBall (0 : Vec d) n, g x i * φ x) := by
          have hloc (u : Vec d → ℝ)
              (hu : ∀ n : ℕ, MemLp u 2 (volume.restrict (Metric.closedBall (0 : Vec d) n))) :
              LocallyIntegrable u volume := by
            intro x
            obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
            refine ⟨Metric.closedBall 0 (n : ℝ), Metric.closedBall_mem_nhds_of_mem ?_, ?_⟩
            · simpa only [Metric.mem_ball, dist_zero_right] using hn
            · let : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : Vec d) n)) :=
                isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : Vec d) (n : ℝ)).measure_ne_top
              exact (hu n).integrable (by norm_num)
          have heq (n : ℕ) (φ : Vec d → ℝ)
              (hs : tsupport φ ⊆ Metric.closedBall (0 : Vec d) n) (i : Fin d) :
              (∫ x in Metric.closedBall (0 : Vec d) n, f x * coordinateDerivative i φ x) =
                (∫ x, f x * coordinateDerivative i φ x) ∧
              (∫ x in Metric.closedBall (0 : Vec d) n, g x i * φ x) =
                (∫ x, g x i * φ x) := by
            constructor
            · apply setIntegral_eq_integral_of_forall_compl_eq_zero
              intro x hx
              have hn : x ∉ tsupport φ := fun ht => hx (hs ht)
              simp only [coordinateDerivative, fderiv_of_notMem_tsupport ℝ hn,
                zero_apply, mul_zero]
            · apply setIntegral_eq_integral_of_forall_compl_eq_zero
              intro x hx
              have hn : x ∉ tsupport φ := fun ht => hx (hs ht)
              have hz : φ x = 0 := (notMem_tsupport_iff_eventuallyEq.mp hn).self_of_nhds
              rw [hz, mul_zero]
          constructor
          · intro hw n φ hφ hs i
            rw [(heq n φ hs i).1, (heq n φ hs i).2]
            simpa only [Measure.restrict_univ] using (hw i).2.2 φ hφ
          · intro hw i
            refine ⟨locallyIntegrableOn_univ.mpr (hloc f hf),
              locallyIntegrableOn_univ.mpr (hloc (fun x => g x i) (fun n => hg n i)), ?_⟩
            intro φ hφ
            obtain ⟨R, hR⟩ := hφ.2.1.isBounded.subset_closedBall (0 : Vec d)
            obtain ⟨n, hn⟩ := exists_nat_gt R
            have hs : tsupport φ ⊆ Metric.closedBall (0 : Vec d) n :=
              hR.trans (Metric.closedBall_subset_closedBall hn.le)
            simpa only [(heq n φ hs i).1, (heq n φ hs i).2, Measure.restrict_univ]
              using hw n φ hφ hs i
        have hnorm {X : Type} [MeasurableSpace X] (μ : Measure X) {d : ℕ}
            (g : X → Vec d) (hg : ∀ i, AEStronglyMeasurable (fun x => g x i) μ) :
            MemLp (fun x => euclideanNorm (g x)) 2 μ ↔
              ∀ i, MemLp (fun x => g x i) 2 μ := by
          have hm : AEStronglyMeasurable (fun x => euclideanNorm (g x)) μ := by
            unfold euclideanNorm euclideanSq dot
            exact Real.continuous_sqrt.comp_aestronglyMeasurable
              (Finset.aestronglyMeasurable_fun_sum _ (fun i _ => (hg i).mul (hg i)))
          constructor
          · intro h i
            apply h.of_le (hg i)
            apply Filter.Eventually.of_forall
            intro x
            have habs : |g x i| ≤ euclideanNorm (g x) := by
              unfold euclideanNorm euclideanSq dot
              apply Real.abs_le_sqrt
              simpa only [sq] using
                (Finset.single_le_sum (f := fun j => g x j * g x j)
                  (fun j _ => mul_self_nonneg (g x j)) (Finset.mem_univ i))
            change |g x i| ≤ |euclideanNorm (g x)|
            exact habs.trans (le_abs_self _)
          · intro h
            have hs : MemLp (fun x => ∑ i, |g x i|) 2 μ := by
              simpa only [Real.norm_eq_abs] using
                memLp_finsetSum Finset.univ (fun i _ => (h i).norm)
            apply hs.of_le hm
            apply Filter.Eventually.of_forall
            intro x
            have hsq : (∑ i, g x i * g x i) ≤ (∑ i, |g x i|) ^ 2 := by
              calc ∑ i, g x i * g x i = ∑ i, |g x i| * |g x i| :=
                    Finset.sum_congr rfl (fun i _ => (abs_mul_abs_self (g x i)).symm)
                _ ≤ ∑ i, ∑ j, |g x i| * |g x j| :=
                    Finset.sum_le_sum (fun i hi => Finset.single_le_sum
                      (f := fun j => |g x i| * |g x j|)
                      (fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)) hi)
                _ = (∑ i, |g x i|) ^ 2 := by rw [sq, Finset.sum_mul_sum]
            change |Real.sqrt (∑ i, g x i * g x i)| ≤ |(∑ i, |g x i|)|
            rw [abs_of_nonneg (Real.sqrt_nonneg _),
              abs_of_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _))]
            calc Real.sqrt (∑ i, g x i * g x i) ≤ Real.sqrt ((∑ i, |g x i|) ^ 2) :=
                  Real.sqrt_le_sqrt hsq
              _ = ∑ i, |g x i| := Real.sqrt_sq (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
        have hdiv {d : ℕ} (F : Vec d → Vec d)
            (hF : ∀ (n : ℕ) (i : Fin d),
              MemLp (fun x => F x i) 2 (volume.restrict (Metric.closedBall (0 : Vec d) n))) :
            HasWeakDivergence Set.univ F (fun _ => 0) ↔
              ∀ (n : ℕ) (φ : Vec d → ℝ), IsSpatialTest Set.univ φ →
                tsupport φ ⊆ Metric.closedBall (0 : Vec d) n →
                  (∫ x in Metric.closedBall (0 : Vec d) n, dot (F x) (gradient φ x)) = 0 := by
          have hloc (i : Fin d) : LocallyIntegrableOn (fun x => F x i) Set.univ volume := by
            apply locallyIntegrableOn_univ.mpr
            intro x
            obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
            refine ⟨Metric.closedBall 0 (n : ℝ), Metric.closedBall_mem_nhds_of_mem ?_, ?_⟩
            · simpa only [Metric.mem_ball, dist_zero_right] using hn
            · let : IsFiniteMeasure (volume.restrict (Metric.closedBall (0 : Vec d) n)) :=
                isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : Vec d) (n : ℝ)).measure_ne_top
              exact (hF n i).integrable (by norm_num)
          have heq (n : ℕ) (φ : Vec d → ℝ)
              (hs : tsupport φ ⊆ Metric.closedBall (0 : Vec d) n) :
              (∫ x in Metric.closedBall (0 : Vec d) n, dot (F x) (gradient φ x)) =
                (∫ x, dot (F x) (gradient φ x)) := by
            apply setIntegral_eq_integral_of_forall_compl_eq_zero
            intro x hx
            have hn : x ∉ tsupport φ := fun ht => hx (hs ht)
            have hz : gradient φ x = 0 := by
              funext i
              simp only [gradient, coordinateDerivative, fderiv_of_notMem_tsupport ℝ hn, zero_apply,
                Pi.zero_apply]
            simp only [hz, dot, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
          constructor
          · intro hw n φ hφ hs
            rw [heq n φ hs]
            simpa only [Measure.restrict_univ, zero_mul, integral_zero, neg_zero] using hw.2.2 φ hφ
          · intro hw
            refine ⟨hloc, locallyIntegrableOn_zero, ?_⟩
            intro φ hφ
            obtain ⟨R, hR⟩ := hφ.2.1.isBounded.subset_closedBall (0 : Vec d)
            obtain ⟨n, hn⟩ := exists_nat_gt R
            have hs : tsupport φ ⊆ Metric.closedBall (0 : Vec d) n :=
              hR.trans (Metric.closedBall_subset_closedBall hn.le)
            simpa only [heq n φ hs, Measure.restrict_univ, zero_mul, integral_zero, neg_zero]
              using hw n φ hφ hs
        have hflux {d : ℕ} {K : ℝ} (hK : 0 ≤ K) (a : Coefficient d K)
            (S : Set (Vec d)) (g : Vec d → Vec d)
            (hg : ∀ i, MemLp (fun x => g x i) 2 (volume.restrict S)) :
            ∀ i, MemLp (fun x => (a x).mulVec (g x) i) 2 (volume.restrict S) := by
          have hb (x : Vec d) (i j : Fin d) : |a.field x i j| ≤ K := by
            have hn (ξ : Vec d) : 0 ≤ euclideanSq ξ := by
              unfold euclideanSq dot
              exact Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)
            exact abs_entry_le_of_quadratic_bounds hK (a.field x) (a.symmetric x)
              (fun ξ => (hn ξ).trans (a.elliptic x ξ).1) (fun ξ => (a.elliptic x ξ).2) i j
          have hm (i j : Fin d) : MemLp (fun x => a.field x i j * g x j) 2
              (volume.restrict S) := by
            apply (hg j).of_le_mul (c := K)
              (((a.locally_integrable i j).aestronglyMeasurable.restrict).mul (hg j).aestronglyMeasurable)
            apply Filter.Eventually.of_forall
            intro x
            change ‖a.field x i j * g x j‖ ≤ K * ‖g x j‖
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_right (by simpa only [Real.norm_eq_abs] using hb x i j)
              (norm_nonneg _)
          intro i
          simpa only [Matrix.mulVec, dotProduct] using
            memLp_finsetSum Finset.univ (fun j _ => hm i j)
        have hbounded {d : ℕ} (φ : Vec d → ℝ) (hφ : IsSpatialTest Set.univ φ) :
            (Measurable φ ∧ ∃ C : NNReal, ∀ x, ‖φ x‖ ≤ C) ∧
            ∀ i : Fin d, Measurable (coordinateDerivative i φ) ∧
              ∃ C : NNReal, ∀ x, ‖coordinateDerivative i φ x‖ ≤ C := by
          have hb (f : Vec d → ℝ) (hc : Continuous f) (hs : HasCompactSupport f) :
              ∃ C : NNReal, ∀ x, ‖f x‖ ≤ C := by
            obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
            exact ⟨⟨max C 0, le_max_right _ _⟩, fun x => (hC x).trans (le_max_left _ _)⟩
          refine ⟨⟨hφ.1.continuous.measurable, hb φ hφ.1.continuous hφ.2.1⟩, ?_⟩
          intro i
          have hc : Continuous (coordinateDerivative i φ) := by
            exact (hφ.1.continuous_fderiv_apply (by simp)).comp
              (continuous_id.prodMk (continuous_const : Continuous (fun _ : Vec d => unitVector i)))
          have hs : HasCompactSupport (coordinateDerivative i φ) :=
            hφ.2.1.fderiv_apply ℝ (unitVector i)
          exact ⟨hc.measurable, hb _ hc hs⟩
        have hpair {X : Type} [MeasurableSpace X] (μ : Measure X) {d : ℕ}
            (a : X → Mat d) (g ψ : X → Vec d)
            (ha : ∀ i j, MemLp (fun x => a x i j) 2 μ)
            (hg : ∀ j, MemLp (fun x => g x j) 2 μ)
            (hψ : ∀ i, AEStronglyMeasurable (fun x => ψ x i) μ)
            (C : Fin d → NNReal) (hC : ∀ i, ∀ᵐ x ∂μ, ‖ψ x i‖ ≤ C i) :
            (∫ x, dot ((a x).mulVec (g x)) (ψ x) ∂μ) =
              ∑ i, ∑ j, ∫ x, ψ x i * a x i j * g x j ∂μ := by
          have hi (i j : Fin d) : Integrable (fun x => ψ x i * a x i j * g x j) μ := by
            have hm : MemLp (fun x => ψ x i * a x i j) 2 μ := by
              apply (ha i j).of_le_mul (c := (C i : ℝ)) ((hψ i).mul (ha i j).aestronglyMeasurable)
              filter_upwards [hC i] with x hx
              change ‖ψ x i * a x i j‖ ≤ (C i : ℝ) * ‖a x i j‖
              rw [norm_mul]
              exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
            exact hm.integrable_mul (hg j)
          have heq (x : X) : dot ((a x).mulVec (g x)) (ψ x) =
              ∑ i, ∑ j, ψ x i * a x i j * g x j := by
            simp only [dot, Matrix.mulVec, dotProduct, Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            ring
          calc
            _ = ∫ x, ∑ i, ∑ j, ψ x i * a x i j * g x j ∂μ :=
              integral_congr_ae (Filter.Eventually.of_forall heq)
            _ = ∑ i, ∫ x, ∑ j, ψ x i * a x i j * g x j ∂μ :=
              integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))
            _ = _ := Finset.sum_congr rfl (fun i _ => integral_finsetSum _ (fun j _ => hi i j))
        have hgrowth {d : ℕ} (f : Vec d → ℝ)
            (U : ∀ n : ℕ, Lp ℝ 2 (volume.restrict (Metric.closedBall (0 : Vec d) n)))
            (hU : ∀ n, U n =ᵐ[volume.restrict (Metric.closedBall (0 : Vec d) n)] f) :
            Filter.Tendsto (fun R : ℝ => R ^ (-2 : ℤ) *
              Real.sqrt (⨍ x in ball (0 : Vec d) R, |f x| ^ 2)) Filter.atTop (nhds 0) ↔
            Filter.Tendsto (fun n : ℕ => ‖U n‖ ^ 2 / (n : ℝ) ^ (d + 4))
              Filter.atTop (nhds 0) := by
          have hnormal {d : ℕ} (f : Vec d → ℝ) :
              Filter.Tendsto (fun R : ℝ => R ^ (-2 : ℤ) *
                Real.sqrt (⨍ x in ball (0 : Vec d) R, |f x| ^ 2)) Filter.atTop (nhds 0) ↔
              Filter.Tendsto (fun R : ℝ =>
                (∫ x in ball (0 : Vec d) R, (f x) ^ 2) / R ^ (d + 4))
                Filter.atTop (nhds 0) := by
            let V := volume.real (ball (0 : Vec d) 1)
            let A (R : ℝ) := ∫ x in ball (0 : Vec d) R, (f x) ^ 2
            let g (R : ℝ) := R ^ (-2 : ℤ) *
              Real.sqrt (⨍ x in ball (0 : Vec d) R, |f x| ^ 2)
            have hV : 0 < V := Correctors.ball_volume_pos_finite d 1 zero_lt_one
            have hA (R : ℝ) : 0 ≤ A R := integral_nonneg (fun x => sq_nonneg (f x))
            have hball (R : ℝ) (hR : 0 < R) :
                volume.real (ball (0 : Vec d) R) = R ^ d * V :=
              Correctors.volume_real_euclideanBall R hR
            have hsquare (R : ℝ) (hR : 0 < R) :
                g R ^ 2 = (A R / R ^ (d + 4)) / V := by
              have hav : (⨍ x in ball (0 : Vec d) R, |f x| ^ 2) =
                  (R ^ d * V)⁻¹ * A R := by
                simp only [setAverage_eq, smul_eq_mul, hball R hR, sq_abs, A]
              have hn : 0 ≤ (R ^ d * V)⁻¹ * A R := by positivity
              dsimp only [g]
              rw [mul_pow, hav, Real.sq_sqrt hn]
              simp only [zpow_neg, zpow_ofNat]
              field_simp
              ring
            change Filter.Tendsto g _ _ ↔ Filter.Tendsto (fun R => A R / R ^ (d + 4)) _ _
            constructor
            · intro h
              have ht := (h.pow 2).mul_const V
              have ht0 : Filter.Tendsto (fun R => g R ^ 2 * V) Filter.atTop (nhds 0) := by
                simpa only [zero_pow (by decide : 2 ≠ 0), zero_mul] using ht
              apply ht0.congr'
              filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with R hR
              rw [hsquare R hR, div_mul_cancel₀ _ hV.ne']
            · intro h
              have ht := Real.continuous_sqrt.continuousAt.tendsto.comp (h.div_const V)
              have ht0 : Filter.Tendsto
                  (fun R => Real.sqrt ((A R / R ^ (d + 4)) / V))
                  Filter.atTop (nhds 0) := by
                simpa only [zero_div, Real.sqrt_zero, Function.comp_def] using ht
              apply ht0.congr'
              filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with R hR
              have hn : 0 ≤ (A R / R ^ (d + 4)) / V := by positivity
              have hg : 0 ≤ g R := mul_nonneg (zpow_nonneg hR.le _) (Real.sqrt_nonneg _)
              nlinarith [hsquare R hR, Real.sq_sqrt hn, Real.sqrt_nonneg
                ((A R / R ^ (d + 4)) / V)]
          have hcompare (A B : ℝ → ℝ) (k : ℕ) (c : ℝ) (hc : 0 < c)
              (hA : ∀ R, 0 ≤ A R) (hB : ∀ R, 0 ≤ B R)
              (hab : ∀ R, 0 < R → A R ≤ B R ∧ B R ≤ A (c * R)) :
              Filter.Tendsto (fun R : ℝ => A R / R ^ k) Filter.atTop (nhds 0) ↔
                Filter.Tendsto (fun R : ℝ => B R / R ^ k) Filter.atTop (nhds 0) := by
            constructor
            · intro h
              have ht := (h.comp ((tendsto_const_mul_atTop_of_pos hc).2 Filter.tendsto_id)).const_mul (c ^ k)
              have ht0 : Filter.Tendsto (fun R : ℝ => c ^ k * (A (c * R) / (c * R) ^ k))
                  Filter.atTop (nhds 0) := by
                simpa only [mul_zero, Function.comp_def, id_eq] using ht
              have heq : (fun R : ℝ => c ^ k * (A (c * R) / (c * R) ^ k)) =
                  (fun R : ℝ => A (c * R) / R ^ k) := by
                funext R
                rw [mul_pow]
                field_simp [hc.ne']
              rw [heq] at ht0
              apply squeeze_zero' _ _ ht0
              · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with R hR
                exact div_nonneg (hB R) (pow_nonneg hR.le k)
              · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with R hR
                exact div_le_div_of_nonneg_right (hab R hR).2 (pow_nonneg hR.le k)
            · intro h
              apply squeeze_zero' _ _ h
              · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with R hR
                exact div_nonneg (hA R) (pow_nonneg hR.le k)
              · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with R hR
                exact div_le_div_of_nonneg_right (hab R hR).1 (pow_nonneg hR.le k)
          have hmass {d : ℕ} (f : Vec d → ℝ)
              (hf : ∀ R : ℝ, MemLp f 2 (volume.restrict (Metric.closedBall (0 : Vec d) R)))
              (R : ℝ) (hR : 0 < R) :
              (∫ x in ball (0 : Vec d) R, (f x) ^ 2) ≤
                  (∫ x in Metric.closedBall (0 : Vec d) R, (f x) ^ 2) ∧
              (∫ x in Metric.closedBall (0 : Vec d) R, (f x) ^ 2) ≤
                  ∫ x in ball (0 : Vec d) (2 * ((d : ℝ) + 1) * R), (f x) ^ 2 := by
            have hlo (v : Vec d) : ‖v‖ ≤ euclideanNorm v := by
              apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
              intro i
              rw [Real.norm_eq_abs]
              apply Real.abs_le_sqrt
              have hs : v i * v i ≤ ∑ j, v j * v j :=
                Finset.single_le_sum (f := fun j => v j * v j) (fun j _ => mul_self_nonneg _)
                  (Finset.mem_univ i)
              simpa only [euclideanSq, dot, sq] using hs
            have hsub (T : ℝ) : ball (0 : Vec d) T ⊆ Metric.closedBall (0 : Vec d) T := by
              intro x hx
              have hx' : euclideanNorm x < T := by simpa only [ball, Set.mem_ofPred_eq, sub_zero] using hx
              simpa only [Metric.mem_closedBall, dist_zero_right] using (hlo x).trans hx'.le
            have hlarge : Metric.closedBall (0 : Vec d) R ⊆
                ball (0 : Vec d) (2 * ((d : ℝ) + 1) * R) := by
              intro x hx
              have hx' : ‖x‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hx
              change euclideanNorm (x - 0) < _
              rw [sub_zero]
              calc euclideanNorm x ≤ ((d : ℝ) + 1) * ‖x‖ := euclideanNorm_le_dimension_mul_norm x
                _ ≤ ((d : ℝ) + 1) * R := mul_le_mul_of_nonneg_left hx' (by positivity)
                _ < 2 * ((d : ℝ) + 1) * R := by
                  have hp : 0 < ((d : ℝ) + 1) * R := mul_pos (by positivity) hR
                  nlinarith
            constructor
            · exact integral_mono_measure (Measure.restrict_mono_set volume (hsub R))
                (Filter.Eventually.of_forall (fun x => sq_nonneg (f x))) (hf R).integrable_sq
            · exact integral_mono_measure (Measure.restrict_mono_set volume hlarge)
                (Filter.Eventually.of_forall (fun x => sq_nonneg (f x)))
                ((hf _).mono_measure (Measure.restrict_mono_set volume (hsub _))).integrable_sq
          have hdiscrete (A : ℝ → ℝ) (hA : Monotone A) (hA0 : ∀ R, 0 ≤ A R) (k : ℕ) :
              Filter.Tendsto (fun R : ℝ => A R / R ^ k) Filter.atTop (nhds 0) ↔
                Filter.Tendsto (fun n : ℕ => A n / (n : ℝ) ^ k) Filter.atTop (nhds 0) := by
            constructor
            · intro h
              exact h.comp tendsto_natCast_atTop_atTop
            · intro h
              have hceil : Filter.Tendsto (Nat.ceil : ℝ → ℕ) Filter.atTop Filter.atTop := by
                apply Filter.tendsto_atTop.2
                intro n
                filter_upwards [Filter.eventually_ge_atTop (n : ℝ)] with R hR
                exact_mod_cast hR.trans (Nat.le_ceil R)
              have hlim : Filter.Tendsto
                  (fun R : ℝ => (2 : ℝ) ^ k * (A (Nat.ceil R) / (Nat.ceil R : ℝ) ^ k))
                  Filter.atTop (nhds 0) := by
                simpa only [mul_zero, Function.comp_def] using tendsto_const_nhds.mul (h.comp hceil)
              apply squeeze_zero' _ _ hlim
              · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with R hR
                exact div_nonneg (hA0 R) (pow_nonneg (by linarith) k)
              · filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with R hR
                have hRp : 0 < R := by linarith
                have hN : R ≤ (Nat.ceil R : ℝ) := Nat.le_ceil R
                have hNp : 0 < (Nat.ceil R : ℝ) := hRp.trans_le hN
                have hN2 : (Nat.ceil R : ℝ) ≤ 2 * R := by
                  have := Nat.ceil_lt_add_one (by linarith : 0 ≤ R)
                  linarith
                have hp : (Nat.ceil R : ℝ) ^ k ≤ (2 * R) ^ k :=
                  pow_le_pow_left₀ (Nat.cast_nonneg _) hN2 k
                rw [← mul_div_assoc]
                apply (div_le_div_iff₀ (pow_pos hRp k) (pow_pos hNp k)).2
                calc
                  A R * (Nat.ceil R : ℝ) ^ k ≤ A (Nat.ceil R) * (2 * R) ^ k :=
                    mul_le_mul (hA hN) hp (pow_nonneg (Nat.cast_nonneg _) k) (hA0 _)
                  _ = ((2 : ℝ) ^ k * A (Nat.ceil R)) * R ^ k := by rw [mul_pow]; ring
          have hfN (n : ℕ) : MemLp f 2 (volume.restrict (Metric.closedBall (0 : Vec d) n)) :=
            (Lp.memLp (U n)).ae_eq (hU n)
          have hf (R : ℝ) : MemLp f 2 (volume.restrict (Metric.closedBall (0 : Vec d) R)) := by
            obtain ⟨n, hn⟩ := exists_nat_gt R
            exact (hfN n).mono_measure (Measure.restrict_mono_set volume
              (Metric.closedBall_subset_closedBall hn.le))
          let A (R : ℝ) := ∫ x in ball (0 : Vec d) R, (f x) ^ 2
          let B (R : ℝ) := ∫ x in Metric.closedBall (0 : Vec d) R, (f x) ^ 2
          have hA (R : ℝ) : 0 ≤ A R := integral_nonneg (fun x => sq_nonneg (f x))
          have hB (R : ℝ) : 0 ≤ B R := integral_nonneg (fun x => sq_nonneg (f x))
          have hmono : Monotone B := by
            intro R S hRS
            exact integral_mono_measure (Measure.restrict_mono_set volume
              (Metric.closedBall_subset_closedBall hRS))
              (Filter.Eventually.of_forall (fun x => sq_nonneg (f x))) (hf S).integrable_sq
          have heq (n : ℕ) : ‖U n‖ ^ 2 = B n := by
            rw [← real_inner_self_eq_norm_sq, L2.inner_def]
            apply integral_congr_ae
            filter_upwards [hU n] with x hx
            simp only [hx, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
          calc
            _ ↔ Filter.Tendsto (fun R : ℝ => A R / R ^ (d + 4)) Filter.atTop (nhds 0) := hnormal f
            _ ↔ Filter.Tendsto (fun R : ℝ => B R / R ^ (d + 4)) Filter.atTop (nhds 0) :=
              hcompare A B (d + 4) (2 * ((d : ℝ) + 1)) (by positivity) hA hB
                (fun R hR => hmass f hf R hR)
            _ ↔ Filter.Tendsto (fun n : ℕ => B n / (n : ℝ) ^ (d + 4)) Filter.atTop (nhds 0) :=
              hdiscrete B hmono hB (d + 4)
            _ ↔ _ := by simp only [heq]

        let S := fun n : ℕ => Metric.closedBall (0 : Vec d) (n : ℝ)
        let μ := fun n : ℕ => volume.restrict (S n)
        have hcover (x : Vec d) : ∃ n : ℕ, x ∈ S n := by
          obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
          exact ⟨n, by simpa only [S, Metric.mem_closedBall, dist_zero_right] using hn.le⟩
        have hrestrict (f : Vec d → ℝ)
            (V : ∀ n : ℕ, Lp ℝ 2 (μ n)) (hV : ∀ n, V n =ᵐ[μ n] f) (n m : ℕ) :
            (V n : Vec d → ℝ) =ᵐ[volume.restrict (S n ∩ S m)] V m := by
          exact ((hV n).filter_mono (ae_mono (Measure.restrict_mono_set volume
            Set.inter_subset_left))).trans ((hV m).filter_mono
            (ae_mono (Measure.restrict_mono_set volume Set.inter_subset_right))).symm
        have hpotentialEq (f : Vec d → ℝ) (hU : ∀ n, U n =ᵐ[μ n] f)
            (n : ℕ) (θ : Vec d → ℝ) :
            (∫ x in Metric.closedBall (0 : Vec d) n, U n x * θ x) = ∫ x in Metric.closedBall (0 : Vec d) n, f x * θ x := by
          apply integral_congr_ae
          filter_upwards [hU n] with x hx
          rw [hx]
        have hgradientEq (g : Vec d → Vec d)
            (hG : ∀ n i, G n i =ᵐ[μ n] (fun x => g x i))
            (n : ℕ) (θ : Vec d → ℝ) (i : Fin d) :
            (∫ x in Metric.closedBall (0 : Vec d) n, G n i x * θ x) = ∫ x in Metric.closedBall (0 : Vec d) n, g x i * θ x := by
          apply integral_congr_ae
          filter_upwards [hG n i] with x hx
          rw [hx]
        have hfluxEq (g : Vec d → Vec d)
            (hG : ∀ n i, G n i =ᵐ[μ n] (fun x => g x i))
            (n : ℕ) (φ : Vec d → ℝ) (hφ : IsSpatialTest Set.univ φ) :
            (∫ x in Metric.closedBall (0 : Vec d) n, dot ((a x).mulVec (g x)) (gradient φ x)) =
              ∑ i, ∑ j, ∫ x in Metric.closedBall (0 : Vec d) n, coordinateDerivative i φ x * A n i j x * G n j x := by
          have ha (i j : Fin d) : MemLp (fun x => a x i j) 2 (μ n) :=
            (Lp.memLp (A n i j)).ae_eq (hA n i j)
          have hg (i : Fin d) : MemLp (fun x => g x i) 2 (μ n) :=
            (Lp.memLp (G n i)).ae_eq (hG n i)
          let C (i : Fin d) : NNReal := Classical.choose ((hbounded φ hφ).2 i).2
          have hC (i : Fin d) : ∀ᵐ x ∂μ n, ‖gradient φ x i‖ ≤ C i :=
            Filter.Eventually.of_forall (Classical.choose_spec ((hbounded φ hφ).2 i).2)
          rw [hpair (μ n) (fun x => a x) g (gradient φ) ha hg
            (fun i => ((hbounded φ hφ).2 i).1.aestronglyMeasurable) C hC]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          apply integral_congr_ae
          filter_upwards [hA n i j, hG n j] with x hax hgx
          simp only [gradient, hax, hgx]
        constructor
        · rintro ⟨heq, hUcompat, hGcompat, hgr⟩
          obtain ⟨f, hfm, hfu⟩ := (hglue volume S (fun n => measurableSet_closedBall) hcover).2 U hUcompat
          have hgi (i : Fin d) := (hglue volume S (fun n => measurableSet_closedBall) hcover).2
            (fun n => G n i) (fun n m => hGcompat n m i)
          choose v hvm hvg using hgi
          let g : Vec d → Vec d := fun x i => v i x
          have hU (n : ℕ) : U n =ᵐ[μ n] f := (hfu n).symm
          have hG (n : ℕ) (i : Fin d) : G n i =ᵐ[μ n] (fun x => g x i) := (hvg i n).symm
          have hf (n : ℕ) : MemLp f 2 (μ n) := (Lp.memLp (U n)).ae_eq (hU n)
          have hg (n : ℕ) (i : Fin d) : MemLp (fun x => g x i) 2 (μ n) :=
            (Lp.memLp (G n i)).ae_eq (hG n i)
          have hw : HasWeakGradient Set.univ f g := (hweak f g hf hg).2 (by
            intro n φ hφ hs i
            rw [← hpotentialEq f hU n (coordinateDerivative i φ), ← hgradientEq g hG n φ i]
            exact (heq n φ hφ hs).1 i)
          have hh : HasWeakDivergence Set.univ (fun x => (a x).mulVec (g x)) (fun _ => 0) :=
            (hdiv _ (fun n => hflux hK a (S n) g (hg n))).2 (by
              intro n φ hφ hs
              rw [hfluxEq g hG n φ hφ]
              exact (heq n φ hφ hs).2)
          have hlo (x : Vec d) : ‖x‖ ≤ euclideanNorm x := by
            apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
            intro i
            rw [Real.norm_eq_abs]
            apply Real.abs_le_sqrt
            simpa only [euclideanSq, dot, sq] using
              (Finset.single_le_sum (f := fun j => x j * x j)
                (fun j _ => mul_self_nonneg _) (Finset.mem_univ i))
          have hlocal (R : ℝ) (hR : 0 < R) :
              MemLp f 2 (volume.restrict (ball 0 R)) ∧
              MemLp (fun x => euclideanNorm (g x)) 2 (volume.restrict (ball 0 R)) := by
            obtain ⟨n, hn⟩ := exists_nat_gt R
            have hle : volume.restrict (ball (0 : Vec d) R) ≤ μ n := by
              apply Measure.restrict_mono_set volume
              intro x hx
              have hx' : euclideanNorm x < R := by
                simpa only [ball, Set.mem_ofPred_eq, sub_zero] using hx
              simpa only [S, Metric.mem_closedBall, dist_zero_right] using
                (hlo x).trans (hx'.le.trans hn.le)
            exact ⟨(hf n).mono_measure hle,
              ((hnorm (μ n) g (fun i => (hg n i).aestronglyMeasurable)).2 (hg n)).mono_measure hle⟩
          let w : SubquadraticHarmonic a :=
            ⟨f, g, hw, hlocal, hh, (hgrowth f U hU).2 hgr⟩
          exact ⟨w, fun n => ⟨hU n, hG n⟩⟩
        · rintro ⟨w, hw⟩
          have hU (n : ℕ) : U n =ᵐ[μ n] w.potential := (hw n).1
          have hG (n : ℕ) (i : Fin d) : G n i =ᵐ[μ n] (fun x => w.grad x i) := (hw n).2 i
          have hf (n : ℕ) : MemLp w.potential 2 (μ n) := (Lp.memLp (U n)).ae_eq (hU n)
          have hg (n : ℕ) (i : Fin d) : MemLp (fun x => w.grad x i) 2 (μ n) :=
            (Lp.memLp (G n i)).ae_eq (hG n i)
          refine ⟨?_, ?_, ?_, (hgrowth w.potential U hU).1 w.growth⟩
          · intro n φ hφ hs
            constructor
            · intro i
              rw [hpotentialEq w.potential hU n (coordinateDerivative i φ),
                hgradientEq w.grad hG n φ i]
              exact (hweak w.potential w.grad hf hg).1 w.weak_gradient n φ hφ hs i
            · rw [← hfluxEq w.grad hG n φ hφ]
              exact (hdiv _ (fun n => hflux hK a (S n) w.grad (hg n))).1 w.harmonic n φ hφ hs
          · exact hrestrict w.potential U hU
          · intro n m i
            exact hrestrict (fun x => w.grad x i) (fun n => G n i) (fun n => hG n i) n m
    -- A joint Borel evaluator recovers every actual local-L² field almost everywhere.
    have hrepresentative (d : ℕ) :
        let μ := fun n : ℕ => volume.restrict (Metric.closedBall (0 : Vec d) (n : ℝ))
        let W := ∀ n : ℕ, Lp ℝ 2 (μ n)
        let : MeasurableSpace W := borel W
        ∃ R : W → Vec d → ℝ,
          Measurable (fun s : W × Vec d => R s.1 s.2) ∧
          ∀ (u : W) (f : Vec d → ℝ), (∀ n, u n =ᵐ[μ n] f) → R u =ᵐ[volume] f := by
      as_aux_lemma =>
        classical
        have hlocalRepresentative {X : Type} [MeasurableSpace X] (μ : Measure X)
            [IsFiniteMeasure μ] [IsSeparable μ] :
            let : MeasurableSpace (Lp ℝ 2 μ) := borel _
            ∃ R : Lp ℝ 2 μ → X → ℝ,
              Measurable (fun s : Lp ℝ 2 μ × X => R s.1 s.2) ∧
              ∀ u, R u =ᵐ[μ] u := by
          classical
          let : MeasurableSpace (Lp ℝ 2 μ) := borel _
          let : BorelSpace (Lp ℝ 2 μ) := ⟨rfl⟩
          let : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
          let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
          obtain ⟨v, hv⟩ := TopologicalSpace.exists_dense_seq (α := Lp ℝ 2 μ)
          have hex (n : ℕ) (u : Lp ℝ 2 μ) : ∃ k, dist u (v k) < (1 / 2 : ℝ) ^ (n + 2) :=
            hv.exists_dist_lt u (by positivity)
          let ν (n : ℕ) (u : Lp ℝ 2 μ) := Nat.find (hex n u)
          have hν (n : ℕ) : Measurable (ν n) :=
            measurable_find (hex n) (fun k => measurableSet_lt
              (measurable_id.dist measurable_const) measurable_const)
          let V (n : ℕ) (u : Lp ℝ 2 μ) := v (ν n u)
          have hdist (n : ℕ) (u : Lp ℝ 2 μ) :
              dist u (V n u) < (1 / 2 : ℝ) ^ (n + 2) := Nat.find_spec (hex n u)
          have hJ (n : ℕ) : Measurable (fun s : Lp ℝ 2 μ × X => V n s.1 s.2) := by
            have hm : Measurable (fun s : ℕ × X => v s.1 s.2) :=
              measurable_from_prod_countable_right (fun k => (Lp.stronglyMeasurable (v k)).measurable)
            exact hm.comp ((hν n).comp measurable_fst |>.prodMk measurable_snd)
          let R (u : Lp ℝ 2 μ) (x : X) := limsup (fun n => V n u x) atTop
          refine ⟨R, Measurable.limsup hJ, ?_⟩
          intro u
          have hcauchy : ∀ N n m : ℕ, N ≤ n → N ≤ m →
              eLpNorm (fun x => V n u x - V m u x) 2 μ < (1 / 2 : ℝ≥0∞) ^ N := by
            intro N n m hn hm
            have hpn : (1 / 2 : ℝ) ^ (n + 2) ≤ (1 / 2 : ℝ) ^ (N + 2) :=
              pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
            have hpm : (1 / 2 : ℝ) ^ (m + 2) ≤ (1 / 2 : ℝ) ^ (N + 2) :=
              pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
            have hd : dist (V n u) (V m u) < (1 / 2 : ℝ) ^ N := by
              have ht := dist_triangle (V n u) u (V m u)
              have hdn := (hdist n u).trans_le hpn
              have hdm := (hdist m u).trans_le hpm
              rw [dist_comm (V n u) u] at ht
              have hp : 0 < (1 / 2 : ℝ) ^ N := by positivity
              rw [pow_add] at hdn hdm
              norm_num at hdn hdm
              nlinarith
            change eLpNorm ((V n u : X → ℝ) - (V m u : X → ℝ)) 2 μ < _
            rw [← Lp.edist_def, Lp.edist_dist]
            convert ENNReal.ofReal_lt_ofReal_iff (show 0 < (1 / 2 : ℝ) ^ N by positivity) |>.mpr hd using 1
            norm_num [ENNReal.ofReal_pow, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
          have hB : (∑' n : ℕ, (1 / 2 : ℝ≥0∞) ^ n) ≠ ∞ := by
            rw [ENNReal.tsum_geometric]
            norm_num
          have hae := Lp.ae_tendsto_of_cauchy_eLpNorm
            (fun n => Lp.aestronglyMeasurable (V n u)) (show (1 : ℝ≥0∞) ≤ 2 by norm_num) hB hcauchy
          have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => V n u x) atTop (𝓝 (R u x)) := by
            filter_upwards [hae] with x hx
            obtain ⟨l, hl⟩ := hx
            simpa only [R, hl.limsup_eq] using hl
          have hconv : Tendsto (fun n => V n u) atTop (𝓝 u) := by
            apply tendsto_iff_dist_tendsto_zero.mpr
            have ht : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 2)) atTop (𝓝 0) := by
              simpa only [Function.comp_def] using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
                (by norm_num : (1 / 2 : ℝ) < 1)).comp (tendsto_add_atTop_nat 2)
            exact squeeze_zero (fun _ => dist_nonneg) (fun n => by simpa [dist_comm] using (hdist n u).le) ht
          exact tendstoInMeasure_ae_unique
            (tendstoInMeasure_of_tendsto_ae (fun n => Lp.aestronglyMeasurable (V n u)) hlim)
            (tendstoInMeasure_of_tendsto_Lp hconv)

        let S := fun n : ℕ => Metric.closedBall (0 : Vec d) (n : ℝ)
        let μ := fun n : ℕ => volume.restrict (S n)
        let W := ∀ n : ℕ, Lp ℝ 2 (μ n)
        let (n : ℕ) : MeasurableSpace (Lp ℝ 2 (μ n)) := borel _
        let (n : ℕ) : BorelSpace (Lp ℝ 2 (μ n)) := ⟨rfl⟩
        let (n : ℕ) : IsFiniteMeasure (μ n) :=
          isFiniteMeasure_restrict.mpr (isCompact_closedBall (0 : Vec d) (n : ℝ)).measure_ne_top
        let (n : ℕ) : IsSeparable (μ n) := by dsimp [μ, S]; infer_instance
        let : MeasurableSpace W := borel W
        let : BorelSpace W := ⟨rfl⟩
        choose R hRm hRa using fun n : ℕ => hlocalRepresentative (μ n)
        have hcover (x : Vec d) : ∃ n : ℕ, x ∈ S n := by
          obtain ⟨n, hn⟩ := exists_nat_gt ‖x‖
          exact ⟨n, by simpa only [S, Metric.mem_closedBall, dist_zero_right] using hn.le⟩
        let i (x : Vec d) := Nat.find (hcover x)
        have hi : Measurable i := measurable_find hcover (fun n => measurableSet_closedBall)
        let F (u : W) (x : Vec d) := R (i x) (u (i x)) x
        refine ⟨F, ?_, ?_⟩
        · have hrep : Measurable (fun s : ℕ × (W × Vec d) => R s.1 (s.2.1 s.1) s.2.2) := by
            apply measurable_from_prod_countable_right
            intro n
            have hn : Measurable (fun u : W => u n) := (continuous_apply n).measurable
            exact (hRm n).comp ((hn.comp measurable_fst).prodMk measurable_snd)
          exact hrep.comp ((hi.comp measurable_snd).prodMk measurable_id)
        · intro u f hu
          have hn (n : ℕ) : ∀ᵐ x ∂volume, x ∈ S n → R n (u n) x = f x := by
            exact (ae_restrict_iff' measurableSet_closedBall).mp ((hRa n (u n)).trans (hu n))
          filter_upwards [ae_all_iff.mpr hn] with x hx
          exact hx (i x) (Nat.find_spec (hcover x))
    have hobjective {Ω : Type} [MeasurableSpace Ω] {d : ℕ}
        (a : Ω → Vec d → Mat d) (ha : Measurable (fun s : Ω × Vec d => a s.1 s.2))
        (g : Ω → Vec d → Vec d)
        (hg : Measurable (fun s : Ω × Vec d => g s.1 s.2)) (p q z : Vec d) (r : ℝ) :
        Measurable (fun ω => ∫ x, heatKernel z r x *
          (-(1 / 2 : ℝ) * dot (g ω x) ((a ω x).mulVec (g ω x)) -
            dot p ((a ω x).mulVec (g ω x)) + dot q (g ω x))) := by
      as_aux_lemma =>
          let F : Mat d × Vec d → ℝ := fun s =>
            -(1 / 2 : ℝ) * dot s.2 (s.1.mulVec s.2) - dot p (s.1.mulVec s.2) + dot q s.2
          have hd : Continuous (fun s : Vec d × Vec d => dot s.1 s.2) :=
            continuous_fst.dotProduct continuous_snd
          have hflux : Continuous (fun s : Mat d × Vec d => s.1.mulVec s.2) :=
            continuous_fst.matrix_mulVec continuous_snd
          have hF : Continuous F := by
            exact ((continuous_const.mul (hd.comp (continuous_snd.prodMk hflux))).sub
              (hd.comp (continuous_const.prodMk hflux))).add
              (hd.comp (continuous_const.prodMk continuous_snd))
          have hk : Measurable (fun x : Vec d => heatKernel z r x) := by
            exact ((Correctors.continuous_euclideanHeatKernel (d := d) (r ^ 2)).comp
              (continuous_id.sub continuous_const)).measurable
          have hm : Measurable (fun s : Ω × Vec d => heatKernel z r s.2 * F (a s.1 s.2, g s.1 s.2)) :=
            (hk.comp measurable_snd).mul (hF.measurable.comp (ha.prodMk hg))
          exact hm.stronglyMeasurable.integral_prod_right'.measurable

    let μ := fun n : ℕ => volume.restrict (Metric.closedBall (0 : Vec d) (n : ℝ))
    let E := ∀ n : ℕ, Fin d → Fin d → Lp ℝ 2 (μ n)
    let F := ∀ n : ℕ, Lp ℝ 2 (μ n) × (Fin d → Lp ℝ 2 (μ n))
    let W := ∀ n : ℕ, Lp ℝ 2 (μ n)
    let : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
    let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
    let (n : ℕ) : IsSeparable (μ n) := by dsimp [μ]; infer_instance
    let (n : ℕ) : SecondCountableTopology (Lp ℝ 2 (μ n)) := inferInstance
    let : SecondCountableTopology E := inferInstance
    let : SecondCountableTopology F := inferInstance
    let : SecondCountableTopology W := inferInstance
    let : MeasurableSpace E := borel E
    let : MeasurableSpace F := borel F
    let : MeasurableSpace W := borel W
    let : BorelSpace E := ⟨rfl⟩
    let : BorelSpace F := ⟨rfl⟩
    let : BorelSpace W := ⟨rfl⟩
    obtain ⟨C, hPolish, hC, hCa⟩ := hencoding hK
    let : PolishSpace E := hPolish
    let : PolishSpace F := inferInstance
    let := TopologicalSpace.upgradeIsCompletelyMetrizable E
    let G := {s : E × F |
      (∀ (n : ℕ) (φ : Vec d → ℝ), IsSpatialTest Set.univ φ →
        tsupport φ ⊆ Metric.closedBall (0 : Vec d) n →
        (∀ i : Fin d,
          (∫ x in Metric.closedBall (0 : Vec d) n, (s.2 n).1 x * coordinateDerivative i φ x) =
            -(∫ x in Metric.closedBall (0 : Vec d) n, (s.2 n).2 i x * φ x)) ∧
        (∑ i, ∑ j, ∫ x in Metric.closedBall (0 : Vec d) n,
          coordinateDerivative i φ x * s.1 n i j x * (s.2 n).2 j x) = 0) ∧
      (∀ n m : ℕ, ((s.2 n).1 : Vec d → ℝ) =ᵐ[volume.restrict
        (Metric.closedBall (0 : Vec d) n ∩ Metric.closedBall (0 : Vec d) m)] (s.2 m).1) ∧
      (∀ (n m : ℕ) (i : Fin d), ((s.2 n).2 i : Vec d → ℝ) =ᵐ[volume.restrict
        (Metric.closedBall (0 : Vec d) n ∩ Metric.closedBall (0 : Vec d) m)] (s.2 m).2 i) ∧
      Tendsto (fun n : ℕ => ‖(s.2 n).1‖ ^ 2 / (n : ℝ) ^ (d + 4)) atTop (𝓝 0)}
    obtain ⟨hG, hzero⟩ : MeasurableSet G ∧ ∀ A : E,
        (A, fun _ => (0, fun _ => 0)) ∈ G := hgraph d
    obtain ⟨R, hR, hRa⟩ := hrepresentative d
    let Aeval (A : E) (x : Vec d) : Mat d := fun i j => R (fun n => A n i j) x
    let geval (v : F) (x : Vec d) : Vec d := fun i => R (fun n => (v n).2 i) x
    have hAeval : Measurable (fun s : (E × F) × Vec d => Aeval s.1.1 s.2) := by
      change @Measurable _ (Fin d → Fin d → ℝ) _ (borel _) _
      rw [← (Pi.borelSpace (X := fun _ : Fin d => Fin d → ℝ)).measurable_eq]
      apply measurable_pi_iff.mpr
      intro i
      apply measurable_pi_iff.mpr
      intro j
      have hc : Continuous (fun s : E × F => (fun n => s.1 n i j) : (E × F) → W) := by
        fun_prop
      exact hR.comp ((hc.measurable.comp measurable_fst).prodMk measurable_snd)
    have hgeval : Measurable (fun s : (E × F) × Vec d => geval s.1.2 s.2) := by
      apply measurable_pi_iff.mpr
      intro i
      have hc : Continuous (fun s : E × F => (fun n => (s.2 n).2 i) : (E × F) → W) := by
        fun_prop
      exact hR.comp ((hc.measurable.comp measurable_fst).prodMk measurable_snd)
    let obj (s : E × F) := ∫ x, heatKernel z r x *
      (-(1 / 2 : ℝ) * dot (geval s.2 x) ((Aeval s.1 x).mulVec (geval s.2 x)) -
        dot p ((Aeval s.1 x).mulVec (geval s.2 x)) + dot q (geval s.2 x))
    have hobj : Measurable obj :=
      hobjective (Ω := E × F) (d := d) (fun s x => Aeval s.1 x) hAeval
        (fun s x => geval s.2 x) hgeval p q z r
    let energy (a : Coefficient d K) (w : SubquadraticHarmonic a) :=
      ∫ x, heatKernel z r x *
        (-(1 / 2 : ℝ) * dot (w.grad x) ((a x).mulVec (w.grad x)) -
          dot p ((a x).mulVec (w.grad x)) + dot q (w.grad x))
    have hid (a : Coefficient d K) (v : F) (w : SubquadraticHarmonic a)
        (hw : ∀ n, (v n).1 =ᵐ[μ n] w.potential ∧
          ∀ i, (v n).2 i =ᵐ[μ n] (fun x => w.grad x i)) :
        obj (C a, v) = energy a w := by
      have ha (i j : Fin d) : (fun x => Aeval (C a) x i j) =ᵐ[volume]
          (fun x => a x i j) := hRa _ _ (fun n => hCa a n i j)
      have hg (i : Fin d) : (fun x => geval v x i) =ᵐ[volume]
          (fun x => w.grad x i) := hRa _ _ (fun n => (hw n).2 i)
      apply integral_congr_ae
      filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (ha i)),
        ae_all_iff.mpr hg] with x hax hgx
      have hax' : Aeval (C a) x = a x := funext fun i => funext fun j => hax i j
      have hgx' : geval v x = w.grad x := funext hgx
      simp only [hax', hgx']
    have hf (a : Coefficient d K) (v : F) : (C a, v) ∈ G ↔
        ∃ w : SubquadraticHarmonic a, ∀ n, (v n).1 =ᵐ[μ n] w.potential ∧
          ∀ i, (v n).2 i =ᵐ[μ n] (fun x => w.grad x i) :=
      hfiber hK a (C a) (hCa a) (fun n => (v n).1) (fun n => (v n).2)
    let B := K * euclideanSq p + euclideanSq q
    let V (A : E) := sSup {e : ℝ | ∃ v : F, (A, v) ∈ G ∧
      e = min B (max 0 (obj (A, v)))}
    have hVcuts : ∀ t : ℝ, AnalyticSet {A : E | t < V A} :=
      hcuts G hG obj hobj (fun _ => (0, fun _ => 0)) hzero B
    -- Clipping makes every quotient value finite and preserves actual strict upper cuts.
    have hVeq (a : Coefficient d K) : V (C a) = gaussianEnergyJ1 a z r p q := by
      obtain ⟨hnonneg, hbound, hrawcuts⟩ :=
        coarse_gaussianEnergyJ1_bounds_upperCuts a z r hr p q
      have hb : BddAbove {e : ℝ | ∃ v : F, (C a, v) ∈ G ∧
          e = min B (max 0 (obj (C a, v)))} := by
        refine ⟨B, ?_⟩
        rintro e ⟨v, hv, rfl⟩
        exact min_le_left _ _
      have hn : Set.Nonempty {e : ℝ | ∃ v : F, (C a, v) ∈ G ∧
          e = min B (max 0 (obj (C a, v)))} :=
        ⟨_, _, hzero (C a), rfl⟩
      have hlt (t : ℝ) : t < V (C a) ↔ t < gaussianEnergyJ1 a z r p q := by
        change t < sSup _ ↔ _
        rw [lt_csSup_iff hb hn]
        constructor
        · rintro ⟨e, ⟨v, hv, rfl⟩, ht⟩
          by_cases ht0 : t < 0
          · exact ht0.trans_le hnonneg
          obtain ⟨w, hw⟩ := (hf a v).mp hv
          apply (hrawcuts t).mpr
          refine ⟨w, ?_⟩
          have he : t < max 0 (obj (C a, v)) := ht.trans_le (min_le_right _ _)
          have he' : t < obj (C a, v) := (lt_max_iff.mp he).resolve_left ht0
          simpa only [hid a v w hw] using he'
        · intro ht
          obtain ⟨w, hw⟩ := (hrawcuts t).mp ht
          obtain ⟨U, H, hUH⟩ := hclasses w
          let v : F := fun n => (U n, H n)
          have hv : (C a, v) ∈ G := (hf a v).mpr ⟨w, hUH⟩
          refine ⟨_, ⟨v, hv, rfl⟩, lt_min (ht.trans_le hbound) ?_⟩
          apply lt_max_of_lt_right
          rw [hid a v w hUH]
          exact hw
      exact le_antisymm
        (le_of_not_gt fun h => (lt_irrefl _ ((hlt _).mp h)))
        (le_of_not_gt fun h => (lt_irrefl _ ((hlt _).mpr h)))
    have hVm : AEStronglyMeasurable V (Measure.map C P) :=
      coarse_analytic_upperCuts_aestronglyMeasurable (Measure.map C P) V hVcuts
    have hcomp := hVm.comp_measurable hC
    exact hcomp.congr (Filter.Eventually.of_forall hVeq)
  have hρ : 0 < D.dependenceRange := lt_of_lt_of_le zero_lt_one D.one_le_dependenceRange
  have hs : 0 < r / D.dependenceRange := div_pos (hρ.trans_le hr) hρ
  have hK : 0 ≤ AKMUpperEllipticity D.ellipticity := by
    unfold AKMUpperEllipticity
    exact mul_self_nonneg _
  let := actualCoefficientLaw_probability Q
  let A := ellipticityScale D.ellipticity • homogenizedCoefficient Q
  let z := D.dependenceRange⁻¹ • x
  exact ((hGaussian hK (actualCoefficientLaw Q) z _ hs
      (unitVector j + unitVector k) (A.mulVec (unitVector j))).sub
    (hGaussian hK (actualCoefficientLaw Q) z _ hs
      (unitVector j - unitVector k) (A.mulVec (unitVector j)))).div₀
        aestronglyMeasurable_const

-- The exact supervisor contract retains dimension and smooth-law hypotheses;
-- the measurable-value proof establishes this consequence without using them.
attribute [nolint unusedArguments] coarseEntry_signed_aestronglyMeasurable

#print axioms coarseEntry_signed_aestronglyMeasurable
#lint

-- Check the complete local closure, including generated auxiliary declarations.
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
