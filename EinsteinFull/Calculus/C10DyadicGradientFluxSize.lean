import EinsteinFull.Blueprint.G2.node_e_u3A_energy_u2D_target
import EinsteinFull.Frozen.FiniteTimeFlux
import EinsteinFull.Calculus.ComplexForceDriftSupport
import EinsteinFull.Calculus.ComplexGeneratorUniquenessSupport
import EinsteinFull.Blueprint.G2.Proofs.W2EnergyTarget

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- The graph energy bound controls the actual integrated anisotropic gradient flux. -/
theorem dyadic_integrated_gradient_flux_size
    (henergy : node_e_u3A_energy_u2D_targetStmt)
    : ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d), ∃ C : ℝ, 0 < C ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
        (β : Fin d → Lp ℂ 2 (reducedLaw Q))
        (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
        IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
        IsReducedClockObservation Q μ → ∀ ζ : ℂ,
      ∀ (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
        IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
        IsComplexTransposeSemigroup Q P Pdag →
      ∀ (G F : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q)),
        IsFiniteTimeFlux hd Q ζ P Pdag β a μ G F →
      ∀ (s u : ℝ≥0), 1 ≤ (s : ℝ) → s ≤ u → u ≤ 2*s →
        ‖ζ‖ * Real.sqrt (2*(s : ℝ)) ≤ 2 → ∀ ν : FluxIndex d,
        Real.sqrt (∑ j : Fin d,
          ‖∑ k : Fin d, complexCoefficientMul Q j k
            (∫ r in Set.Icc (s : ℝ) (u : ℝ), G r.toNNReal ν k)‖^2) ≤
          C * (s : ℝ) ^ (-(d : ℝ)/4) := by
  have globalEnergy {d : ℕ} (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
      (hQ : IsStationary Q) {ν : Measure ℝ} [SFinite ν]
      (G : ℝ → Fin d → Lp ℂ 2 Q) (g : ℝ × FieldPair d → Fin d → ℂ)
      (hgm : ∀ j, AEStronglyMeasurable (fun z => g z j) (ν.prod Q))
      (hge : ∀ᵐ r ∂ν, ∀ j, (fun ω => g (r, ω) j) =ᵐ[Q] G r j)
      (hi : Integrable (fun r => ∫ ω, ∑ j, ‖g (r, ω) j‖^2 ∂Q) ν) :
      (eLpNorm (fun ω => Real.sqrt (∫ r,
        (⨍ y in {y : Vec d | euclideanNorm y < 1},
          ∑ j, ‖g (r, translate y ω) j‖^2) ∂ν)) 2 Q).toReal =
        Real.sqrt (∫ r, ∑ j, ‖G r j‖^2 ∂ν) := by
    have average (B : Set (Vec d)) [IsFiniteMeasure (volume.restrict B)]
        (hB : 0 < volume.real B) {E : ℝ × FieldPair d → ℝ}
        (hi : Integrable E (ν.prod Q)) :
        Integrable (fun ω => ∫ s, (⨍ y in B, E (s, translate y ω)) ∂ν) Q ∧
        (∫ ω, ∫ s, (⨍ y in B, E (s, translate y ω)) ∂ν ∂Q) =
          ∫ s, (∫ ω, E (s, ω) ∂Q) ∂ν := by
      have spatial (m : Measure (Vec d)) [IsFiniteMeasure m] :
          (∫ ω, ∫ p : Vec d × ℝ, E (p.2, translate p.1 ω) ∂(m.prod ν) ∂Q) =
            m.real univ * ∫ s, ∫ ω, E (s, ω) ∂Q ∂ν := by
        have ht := integrable_joint_spatial_energy Q hQ m hi
        have ha := measurePreserving_prodAssoc m ν Q
        have hb : Integrable (fun p : (Vec d × ℝ) × FieldPair d => E (p.1.2, p.2))
            ((m.prod ν).prod Q) :=
          (ha.integrable_comp (hi.comp_snd m).aestronglyMeasurable).mpr (hi.comp_snd m)
        have hm := (MeasurePreserving.id (m.prod ν)).skew_product
          (g := fun p ω => translate p.1 ω)
          (Probability.continuous_translate.measurable.comp
            ((measurable_fst.fst).prodMk measurable_snd))
          (ae_of_all _ fun p => (measurePreserving_translate Q hQ p.1).map_eq)
        have hbm := hb.aestronglyMeasurable
        rw [← hm.map_eq] at hbm
        have hmi := integral_map hm.measurable.aemeasurable hbm
        have hba := (hi.comp_snd m).aestronglyMeasurable
        rw [← ha.map_eq] at hba
        have hai := integral_map ha.measurable.aemeasurable hba
        rw [hm.map_eq] at hmi
        rw [ha.map_eq] at hai
        rw [← integral_integral_swap ht, ← integral_prod _ ht]
        calc
          _ = ∫ p : (Vec d × ℝ) × FieldPair d, E (p.1.2, p.2)
              ∂((m.prod ν).prod Q) := by simpa [hm.map_eq] using hmi.symm
          _ = ∫ p : Vec d × ℝ × FieldPair d, E p.2 ∂(m.prod (ν.prod Q)) := by
            simpa [ha.map_eq, MeasurableEquiv.prodAssoc] using hai.symm
          _ = _ := by
            rw [integral_prod _ (hi.comp_snd m)]
            simp only [integral_const, smul_eq_mul]
            rw [integral_prod _ hi]
      have ht := integrable_joint_spatial_energy Q hQ (volume.restrict B) hi
      have he : (fun ω => ∫ s, (∫ y in B, E (s, translate y ω)) ∂ν) =ᵐ[Q]
          (fun ω => ∫ p : Vec d × ℝ, E (p.2, translate p.1 ω)
            ∂((volume.restrict B).prod ν)) := by
        filter_upwards [ht.prod_left_ae] with ω hω
        exact (integral_prod_symm _ hω).symm
      have ha := ht.integral_prod_right.congr he.symm
      have hn (ω : FieldPair d) :
          (∫ s, (⨍ y in B, E (s, translate y ω)) ∂ν) =
            (volume.real B)⁻¹ * ∫ s, (∫ y in B, E (s, translate y ω)) ∂ν := by
        simp only [setAverage_eq, smul_eq_mul, integral_const_mul]
      constructor
      · simpa only [hn] using ha.const_mul (volume.real B)⁻¹
      · simp_rw [hn]
        rw [integral_const_mul, integral_congr_ae he, spatial]
        simp only [Measure.real, Measure.restrict_apply_univ]
        rw [← mul_assoc]
        change ((volume.real B)⁻¹ * volume.real B) * _ = _
        rw [inv_mul_cancel₀ hB.ne', one_mul]
    let e : ℝ × FieldPair d → ℝ := fun z => ∑ j, ‖g z j‖^2
    have hn (z : ℝ × FieldPair d) : 0 ≤ e z :=
      Finset.sum_nonneg fun j _ => sq_nonneg _
    have hm : AEStronglyMeasurable e (ν.prod Q) :=
      Finset.aestronglyMeasurable_fun_sum _ fun j _ => (hgm j).norm.pow 2
    have hs : ∀ᵐ r ∂ν, Integrable (fun ω => e (r, ω)) Q ∧
        (∫ ω, e (r, ω) ∂Q) = ∑ j, ‖G r j‖^2 := by
      filter_upwards [hge] with r hr
      have hj (j : Fin d) : Integrable (fun ω => ‖g (r, ω) j‖^2) Q :=
        (Lp.memLp (G r j)).norm.integrable_sq.congr
          ((hr j).symm.mono fun ω h => congrArg (fun z : ℂ => ‖z‖^2) h)
      refine ⟨integrable_finsetSum _ (fun j _ => hj j), ?_⟩
      change (∫ ω, ∑ j, ‖g (r, ω) j‖^2 ∂Q) = _
      rw [integral_finsetSum _ (fun j _ => hj j)]
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_congr_ae ((hr j).mono fun ω h => congrArg (fun z : ℂ => ‖z‖^2) h)]
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      simp only [real_inner_self_eq_norm_sq]
    have hji : Integrable e (ν.prod Q) := by
      apply (integrable_prod_iff hm).mpr
      refine ⟨hs.mono fun r hr => hr.1, ?_⟩
      simpa only [Real.norm_of_nonneg (hn _)] using hi
    let B := {y : Vec d | euclideanNorm y < 1}
    have hB : 0 < volume.real B := by
      simpa only [sub_zero] using localSpatialEnergy_window_volume (0 : Vec d) 1 zero_lt_one
    let : IsFiniteMeasure (volume.restrict B) :=
      isFiniteMeasure_restrict.mpr (ENNReal.toReal_pos_iff.mp hB).2.ne
    obtain ⟨ha, he⟩ := average B hB hji
    have hnon (ω : FieldPair d) : 0 ≤ ∫ r, (⨍ y in B, e (r, translate y ω)) ∂ν := by
      apply integral_nonneg
      intro r
      exact integral_nonneg fun y => hn _
    apply (energyTarget_sqrt_norm ha hnon).2.trans
    apply congrArg Real.sqrt
    exact he.trans (integral_congr_ae (hs.mono fun r hr => hr.2))
  have timeSize {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      {f : ℝ → E} (hf : Continuous f)
      {s u : ℝ} (hs : 0 ≤ s) (hu : u ≤ 2*s) :
      ‖∫ r in Set.Icc s u, f r‖ ≤
        Real.sqrt s * Real.sqrt (∫ r in Set.Icc s (2*s), ‖f r‖^2) := by
    let ν := volume.restrict (Set.Icc s (2*s))
    have hi : Integrable (fun r => ‖f r‖^2) ν :=
      (hf.norm.pow 2).integrableOn_Icc
    have hm : MemLp (fun r => ‖f r‖) 2 ν :=
      (memLp_two_iff_integrable_sq_norm hf.norm.aestronglyMeasurable.restrict).mpr
        (by simpa only [norm_norm] using hi)
    have hc := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
      (by simpa using hm) (by simpa using (memLp_const (μ := ν) (p := 2) (1 : ℝ)))
    have hholder : (∫ r in Set.Icc s (2*s), ‖f r‖) ≤
        Real.sqrt s * Real.sqrt (∫ r in Set.Icc s (2*s), ‖f r‖^2) := by
      have hlen : ν.real Set.univ = s := by
        simp [ν, Measure.real, Real.volume_Icc, show 2*s-s=s by ring, hs]
      simp only [norm_norm, norm_one, Real.rpow_two, one_pow, mul_one,
        integral_const, smul_eq_mul, hlen] at hc
      rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hc
      simpa only [ν, mul_comm] using hc
    apply (norm_integral_le_integral_norm _).trans
    apply le_trans _ hholder
    exact integral_mono_measure (Measure.restrict_mono (Set.Icc_subset_Icc le_rfl hu) le_rfl)
      (ae_of_all _ fun r => norm_nonneg _) hf.norm.integrableOn_Icc
  intro d hd D
  obtain ⟨C₀, hC₀, henergy⟩ := henergy d hd D
  let K := Real.exp (2 * D.ellipticity) * D.ellipticity
  have hK : 0 < K := mul_pos (Real.exp_pos _)
    (lt_of_lt_of_le zero_lt_one D.one_le_ellipticity)
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  refine ⟨(d : ℝ)^2 * K * C₀, by positivity, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag G F hF s u hs hsu hu hz ν
  let := reducedLaw_probability Q
  obtain ⟨H, g, hgm, hge, hgrad, he⟩ :=
    henergy Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag
  let idx : FluxIndex d → EndpointIndex d :=
    fun ν => ν.elim Sum.inl (fun _ => Sum.inr true)
  have hne (ν : FluxIndex d) : idx ν ≠ Sum.inr false := by
    cases ν <;> intro h <;> cases h
  let W := Set.Icc (s : ℝ) (2 * (s : ℝ))
  let E := fun (ι : EndpointIndex d) (ω : FieldPair d) =>
    Real.sqrt (∫ r in W, (⨍ y in {y : Vec d | euclideanNorm y < 1},
      ∑ j, ‖g ι (r, translate y ω) j‖^2))
  obtain ⟨hint, hbound⟩ := he (s : ℝ) hs hz
  have hslice : ∀ᵐ r ∂volume.restrict W, ∀ j,
      (fun ω => g (idx ν) (r, ω) j) =ᵐ[reducedLaw Q] G r.toNNReal ν j := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    have hrpos : 0 < r := lt_of_lt_of_le (by linarith) hr.1
    have hrnn : 0 < (r.toNNReal : ℝ) := by simpa [Real.toNNReal_of_nonneg hrpos.le]
    have huq : H (idx ν) r.toNNReal = G r.toNNReal ν :=
      (hgrad _ (hne ν) _ hrnn).unique (hF.choose_spec.choose_spec.1 _ ν)
    intro j
    have hh := hge (idx ν) (hne ν) r.toNNReal hrnn j
    rw [huq] at hh
    simpa [Real.toNNReal_of_nonneg hrpos.le] using hh
  have hnorm : (eLpNorm (E (idx ν)) 2 (reducedLaw Q)).toReal =
      Real.sqrt (∫ r in W, ∑ j, ‖G r.toNNReal ν j‖^2) :=
    globalEnergy (reducedLaw Q) (reducedLaw_stationary Q)
      (fun r => G r.toNNReal ν) (g (idx ν))
      (fun j => (hgm _ (hne ν) j).mono_measure
        (Measure.prod_mono Measure.restrict_le_self le_rfl)) hslice (hint _ (hne ν)).1
  have hsingle : (eLpNorm (E (idx ν)) 2 (reducedLaw Q)).toReal ≤
      C₀ * (s : ℝ)^(-(1/2+(d : ℝ)/4)) := by
    apply le_trans _ hbound
    cases ν with
    | inl i =>
      exact (Finset.single_le_sum
        (f := fun j : Fin d => (eLpNorm (E (Sum.inl j)) 2 (reducedLaw Q)).toReal)
        (fun j _ => ENNReal.toReal_nonneg) (Finset.mem_univ i)).trans (le_add_of_nonneg_left ENNReal.toReal_nonneg)
    | inr v =>
      exact le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => ENNReal.toReal_nonneg)
  have hcont (k : Fin d) : Continuous (fun r : ℝ => G r.toNNReal ν k) :=
    (hF.choose ν k).comp continuous_real_toNNReal
  have hi (k : Fin d) : IntegrableOn (fun r : ℝ => ‖G r.toNNReal ν k‖^2) W :=
    ((hcont k).norm.pow 2).integrableOn_Icc
  have hisum : IntegrableOn (fun r : ℝ => ∑ j, ‖G r.toNNReal ν j‖^2) W :=
    integrable_finsetSum _ fun j _ => hi j
  let A := Real.sqrt (s : ℝ) * (eLpNorm (E (idx ν)) 2 (reducedLaw Q)).toReal
  have hsize (k : Fin d) : ‖∫ r in Set.Icc (s : ℝ) (u : ℝ), G r.toNNReal ν k‖ ≤ A := by
    apply (timeSize (hcont k) s.coe_nonneg (by exact_mod_cast hu)).trans
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    rw [hnorm]
    apply Real.sqrt_le_sqrt
    apply integral_mono (hi k) hisum
    intro r
    exact Finset.single_le_sum (f := fun j : Fin d => ‖G r.toNNReal ν j‖^2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ k)
  let Y := fun j : Fin d => ∑ k : Fin d, complexCoefficientMul Q j k
    (∫ r in Set.Icc (s : ℝ) (u : ℝ), G r.toNNReal ν k)
  have hY (j : Fin d) : ‖Y j‖ ≤ (d : ℝ)*K*A := by
    calc
      ‖Y j‖ ≤ ∑ k : Fin d, ‖complexCoefficientMul Q j k
          (∫ r in Set.Icc (s : ℝ) (u : ℝ), G r.toNNReal ν k)‖ := norm_sum_le _ _
      _ ≤ ∑ _k : Fin d, K*A := by
        apply Finset.sum_le_sum
        intro k _
        exact ((complexCoefficientMul Q j k).le_opNorm _).trans
          (mul_le_mul (norm_complexCoefficientMul_le Q j k) (hsize k)
            (norm_nonneg _) hK.le)
      _ = _ := by simp; ring
  have hsum : Real.sqrt (∑ j : Fin d, ‖Y j‖^2) ≤ (d : ℝ)^2*K*A := by
    calc
      _ ≤ ∑ j : Fin d, ‖Y j‖ := by
        apply Real.sqrt_le_iff.mpr
        refine ⟨Finset.sum_nonneg (fun j _ => norm_nonneg _), ?_⟩
        exact Finset.sum_sq_le_sq_sum_of_nonneg (fun j _ => norm_nonneg _)
      _ ≤ ∑ _j : Fin d, (d : ℝ)*K*A := Finset.sum_le_sum fun j _ => hY j
      _ = _ := by simp; ring
  have hscale : Real.sqrt (s : ℝ) * (s : ℝ)^(-(1/2+(d : ℝ)/4)) =
      (s : ℝ)^(-(d : ℝ)/4) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by linarith : 0 < (s : ℝ))]
    congr 1
    ring
  apply hsum.trans
  dsimp only [A]
  calc
    _ ≤ (d : ℝ)^2*K*(Real.sqrt (s : ℝ) *
        (C₀*(s : ℝ)^(-(1/2+(d : ℝ)/4)))) := by gcongr
    _ = ((d : ℝ)^2*K*C₀) * (Real.sqrt (s : ℝ) *
        (s : ℝ)^(-(1/2+(d : ℝ)/4))) := by ring
    _ = _ := by rw [hscale]

end EinsteinFull.Blueprint
