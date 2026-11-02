import EinsteinFull.Calculus.U7PhysicalL1Contraction
import EinsteinFull.Calculus.U4PhysicalNashEstimate
import SubdiffusiveProcess.Nash.OrbitEnergy
import SubdiffusiveProcess.Nash.Decay
import SubdiffusiveProcess.Nash.OrbitAverage

open MeasureTheory Set Filter SubdiffusiveProcess.Nash
open scoped ENNReal NNReal Topology RealInnerProductSpace
open EinsteinRelation EinsteinRelation.SpatialDirichlet EinsteinRelation.External.GantertSection7Support

noncomputable section
namespace EinsteinFull

/-- Nash applies to the same physical generator orbit, whose L¹ mass is controlled. -/
theorem u7_unforced_physical_generator_orbit_nash
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : (Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω).generatorDomain)
        (hf : Integrable (f : Lp ℝ 2 (physicalReversibleMeasure ω hd 0))
          (physicalReversibleMeasure ω hd 0)) (t : ℝ≥0),
      let S := Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω
      let u := S t f
      Integrable (u : Vec d → ℝ) (physicalReversibleMeasure ω hd 0) ∧
      (∫ x, |u x| ∂physicalReversibleMeasure ω hd 0) ≤
        ∫ x, |(f : Lp ℝ 2 (physicalReversibleMeasure ω hd 0)) x|
          ∂physicalReversibleMeasure ω hd 0 ∧
      (∫ x, u x ^ 2 ∂physicalReversibleMeasure ω hd 0) ≤
        C * ((Blueprint.gmpPhysicalClosedForm hd ω 0 Λ hΛ hω).form u u) ^
          ((d : ℝ) / (d + 2)) *
        (∫ x, |u x| ∂physicalReversibleMeasure ω hd 0) ^ ((4 : ℝ) / (d + 2)) := by
  obtain ⟨C, hC, hN⟩ := u4_unforced_physical_closedForm_nash hd ω Λ hΛ hω
  refine ⟨C, hC, ?_⟩
  intro f hf t
  let S := Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω
  let F : Lp ℝ 2 (physicalReversibleMeasure ω hd 0) := f
  have hc := u7_unforced_physical_L1_contraction hd ω Λ hΛ hω t F hf (Lp.memLp F)
  rw [Lp.toLp_coeFn] at hc
  refine ⟨hc.1, hc.2, ?_⟩
  apply hN
  · exact Blueprint.gmpPhysicalSemigroup_generator_physicalH1Member hd ω 0 Λ hΛ hω
      ⟨S t f, S.operator_mem_generatorDomain f t⟩
  · exact hc.1

/-- Raising Nash's inequality isolates the energy with the heat-decay exponent. -/
theorem u7_nash_raise (d C A E M : ℝ) (hd : 0 < d) (hC : 0 ≤ C)
    (hA : 0 ≤ A) (hE : 0 ≤ E) (hM : 0 ≤ M)
    (hN : A ≤ C * E ^ (d / (d + 2)) * M ^ (4 / (d + 2))) :
    A ^ (1 + 2 / d) ≤ C ^ (1 + 2 / d) * E * M ^ (4 / d) := by
  have hp : 0 ≤ 1 + 2 / d := by positivity
  have hpow := Real.rpow_le_rpow hA hN hp
  have hde : d + 2 ≠ 0 := by positivity
  have hd0 : d ≠ 0 := ne_of_gt hd
  have h1 : d / (d + 2) * (1 + 2 / d) = 1 := by field_simp
  have h2 : 4 / (d + 2) * (1 + 2 / d) = 4 / d := by field_simp
  rw [Real.mul_rpow (mul_nonneg hC (Real.rpow_nonneg hE _))
    (Real.rpow_nonneg hM _), Real.mul_rpow hC (Real.rpow_nonneg hE _),
    ← Real.rpow_mul hE, ← Real.rpow_mul hM, h1, h2, Real.rpow_one] at hpow
  exact hpow

/-- Quantitative decay for a physical generator orbit, with any positive L¹ bound. -/
theorem u7_unforced_physical_generator_decay
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : (Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω).generatorDomain)
        (hf : Integrable (f : Lp ℝ 2 (physicalReversibleMeasure ω hd 0))
          (physicalReversibleMeasure ω hd 0)) (F : ℝ),
      0 < F → (∫ x, |(f : Lp ℝ 2 (physicalReversibleMeasure ω hd 0)) x|
        ∂physicalReversibleMeasure ω hd 0) ≤ F →
      ∀ (t : ℝ≥0), 0 < t →
      ‖Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω t f‖ ^ 2 ≤
        ((4 / ((d : ℝ) * C ^ (1 + 2 / (d : ℝ)) * F ^ (4 / (d : ℝ)))) * t) ^
          (-(d : ℝ) / 2) := by
  obtain ⟨C, hC, hN⟩ := u7_unforced_physical_generator_orbit_nash hd ω Λ hΛ hω
  refine ⟨C, hC, ?_⟩
  intro f hf F hF hfF t ht
  let S := Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω
  let μ := physicalReversibleMeasure ω hd 0
  have hdR : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hd)
  let K : ℝ := C ^ (1 + 2 / (d : ℝ)) * F ^ (4 / (d : ℝ))
  have hK : 0 < K := by dsimp [K]; positivity
  let c : ℝ := 4 / ((d : ℝ) * K)
  have hc : 0 < c := by dsimp [c]; positivity
  let u : ℝ → ℝ := fun s => ‖S (Real.toNNReal s) f‖ ^ 2
  let v : ℝ → ℝ := fun s => 2 * ⟪S (Real.toNNReal s) (S.generator f),
    S (Real.toNNReal s) f⟫
  by_cases hut : u t = 0
  · have heq : ‖S t f‖ ^ 2 = 0 := by simpa [u] using hut
    rw [heq]
    positivity
  have hutP : 0 < u t := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hut)
  have huA : Antitone u := by
    intro a b hab
    exact pow_le_pow_left₀ (norm_nonneg _) (orbit_norm_antitone S f (Real.toNNReal_mono hab)) 2
  have hpos (s : ℝ) (hs : s ∈ Icc 0 (t : ℝ)) : 0 < u s := hutP.trans_le (huA hs.2)
  have hineq (s : ℝ) (hs : s ∈ Ioo 0 (t : ℝ)) :
      v s ≤ -(((d : ℝ) / 2) * c) * u s ^ (1 + 1 / ((d : ℝ) / 2)) := by
    let E : ℝ := -⟪S (Real.toNNReal s) (S.generator f), S (Real.toNNReal s) f⟫
    let M : ℝ := ∫ x, |S (Real.toNNReal s) f x| ∂μ
    have hE : 0 ≤ E := orbit_energy_nonneg S f hs.1
    have hn := hN f hf (Real.toNNReal s)
    have hM : 0 ≤ M := integral_nonneg fun _ => abs_nonneg _
    have hMF : M ≤ F := hn.2.1.trans hfF
    have hnorm : (∫ x, (S (Real.toNNReal s) f) x ^ 2 ∂μ) = u s := by
      rw [show u s = ‖S (Real.toNNReal s) f‖ ^ 2 from rfl,
        ← real_inner_self_eq_norm_sq, L2.inner_def]
      simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
      rfl
    have heq : (Blueprint.gmpPhysicalClosedForm hd ω 0 Λ hΛ hω).form
        (S (Real.toNNReal s) f) (S (Real.toNNReal s) f) = E :=
      Blueprint.gmpPhysicalSemigroup_orbit_energy_generator hd ω 0 Λ hΛ hω f _
    have hn' : u s ≤ C * E ^ ((d : ℝ) / (d + 2)) * M ^ ((4 : ℝ) / ((d : ℝ) + 2)) := by
      have hnash := hn.2.2
      change (∫ x, (S (Real.toNNReal s) f) x ^ 2 ∂μ) ≤
        C * (Blueprint.gmpPhysicalClosedForm hd ω 0 Λ hΛ hω).form
          (S (Real.toNNReal s) f) (S (Real.toNNReal s) f) ^
          ((d : ℝ) / ((d : ℝ) + 2)) * M ^ ((4 : ℝ) / ((d : ℝ) + 2)) at hnash
      rw [hnorm, heq] at hnash
      exact hnash
    have hraised := u7_nash_raise d C (u s) E M hdR hC.le (sq_nonneg _) hE hM hn'
    have hmass : M ^ (4 / (d : ℝ)) ≤ F ^ (4 / (d : ℝ)) :=
      Real.rpow_le_rpow hM hMF (by positivity)
    have hbound : u s ^ (1 + 2 / (d : ℝ)) ≤ K * E := by
      calc
        _ ≤ C ^ (1 + 2 / (d : ℝ)) * E * M ^ (4 / (d : ℝ)) := hraised
        _ ≤ C ^ (1 + 2 / (d : ℝ)) * E * F ^ (4 / (d : ℝ)) := by gcongr
        _ = K * E := by dsimp [K]; ring
    have he : u s ^ (1 + 2 / (d : ℝ)) / K ≤ E := (div_le_iff₀ hK).2 (by simpa [mul_comm] using hbound)
    calc
      v s = -2 * E := by dsimp [v, E]; ring
      _ ≤ -2 * (u s ^ (1 + 2 / (d : ℝ)) / K) :=
        mul_le_mul_of_nonpos_left he (by norm_num)
      _ = -(((d : ℝ) / 2) * c) * u s ^ (1 + 1 / ((d : ℝ) / 2)) := by
        have hex : 1 + 1 / ((d : ℝ) / 2) = 1 + 2 / (d : ℝ) := by field_simp
        rw [hex]
        dsimp [c]
        field_simp [ne_of_gt hdR, ne_of_gt hK] <;> ring
  have hdec := decay_rpow u v ((d : ℝ) / 2) c t (by positivity) hc ht
    (((S.continuous_operator_toNNReal f).norm.pow 2).continuousOn) hpos
    (fun s hs => hasDerivAt_orbit_norm_sq S f hs.1) hineq
  simpa only [u, c, K, S, Real.toNNReal_coe, mul_assoc, neg_div] using hdec

/-- The physical orbit remains inside its initial L¹ ball. -/
theorem u7_physical_orbit_eLpNorm_one_le
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd 0))
    (hf : Integrable (f : Vec d → ℝ) (physicalReversibleMeasure ω hd 0)) (t : ℝ≥0) :
    eLpNorm (Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω t f : Vec d → ℝ) 1
      (physicalReversibleMeasure ω hd 0) ≤
    eLpNorm (f : Vec d → ℝ) 1 (physicalReversibleMeasure ω hd 0) := by
  let μ := physicalReversibleMeasure ω hd 0
  let S := Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω
  have h := u7_unforced_physical_L1_contraction hd ω Λ hΛ hω t f hf (Lp.memLp f)
  rw [Lp.toLp_coeFn] at h
  rw [eLpNorm_one_eq_lintegral_enorm h.1.aestronglyMeasurable,
    eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm h.1,
    ← ofReal_integral_norm_eq_lintegral_enorm hf]
  exact ENNReal.ofReal_le_ofReal (by simpa only [Real.norm_eq_abs] using h.2)

/-- Generator-domain orbit averages inherit the physical L¹ bound. -/
theorem u7_physical_orbitAverage_eLpNorm_one_le
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd 0))
    (hf : Integrable (f : Vec d → ℝ) (physicalReversibleMeasure ω hd 0))
    (t : ℝ≥0) (ht : 0 < t) :
    let S := Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω
    eLpNorm ((orbitAverage S f t : Lp ℝ 2 (physicalReversibleMeasure ω hd 0)) : Vec d → ℝ) 1
      (physicalReversibleMeasure ω hd 0) ≤
    eLpNorm (f : Vec d → ℝ) 1 (physicalReversibleMeasure ω hd 0) := by
  let μ := physicalReversibleMeasure ω hd 0
  let S := Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω
  have htR : (0 : ℝ) < t := ht
  have h := (convex_L1Ball μ (eLpNorm (f : Vec d → ℝ) 1 μ)).set_average_mem
    (isClosed_L1Ball μ _) (t := Ioc (0 : ℝ) t) (μ := volume)
    (by simpa [Real.volume_Ioc] using (ENNReal.ofReal_pos.mpr htR).ne')
    (by simp [Real.volume_Ioc])
    (ae_of_all _ fun s => u7_physical_orbit_eLpNorm_one_le hd ω Λ hΛ hω f hf (Real.toNNReal s))
    ((S.continuous_operator_toNNReal f).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
  rw [setAverage_eq, measureReal_def, Real.volume_Ioc, sub_zero,
    ENNReal.toReal_ofReal htR.le, ← intervalIntegral.integral_of_le t.coe_nonneg] at h
  exact h

/-- Quantitative physical L¹-to-L² decay, with any positive bound on the L¹ mass. -/
theorem u7_unforced_physical_L1_L2_decay
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (f : Lp ℝ 2 (physicalReversibleMeasure ω hd 0))
        (hf : Integrable (f : Vec d → ℝ) (physicalReversibleMeasure ω hd 0)) (F : ℝ),
      0 < F → (∫ x, |f x| ∂physicalReversibleMeasure ω hd 0) ≤ F →
      ∀ (t : ℝ≥0), 0 < t →
      ‖Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω t f‖ ^ 2 ≤
        ((4 / ((d : ℝ) * C ^ (1 + 2 / (d : ℝ)) * F ^ (4 / (d : ℝ)))) * t) ^
          (-(d : ℝ) / 2) := by
  obtain ⟨C, hC, hN⟩ := u7_unforced_physical_generator_decay hd ω Λ hΛ hω
  refine ⟨C, hC, ?_⟩
  intro f hf F hF hfF t ht
  let μ := physicalReversibleMeasure ω hd 0
  let S := Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω
  have hmass : eLpNorm (f : Vec d → ℝ) 1 μ ≤ ENNReal.ofReal F := by
    rw [eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable,
      ← ofReal_integral_norm_eq_lintegral_enorm hf]
    exact ENNReal.ofReal_le_ofReal (by simpa only [Real.norm_eq_abs] using hfF)
  have hlim : Filter.Tendsto (fun s : ℝ≥0 => ‖S t (orbitAverage S f s : Lp ℝ 2 μ)‖ ^ 2)
      (𝓝[>] 0) (𝓝 (‖S t f‖ ^ 2)) :=
    ((continuous_norm.pow 2).tendsto (S t f)).comp
      (((S t).continuous.tendsto f).comp (tendsto_orbitAverage S f))
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with s hs
  let g : S.generatorDomain := orbitAverage S f s
  have hg : eLpNorm (g : Vec d → ℝ) 1 μ ≤ ENNReal.ofReal F :=
    (u7_physical_orbitAverage_eLpNorm_one_le hd ω Λ hΛ hω f hf s hs).trans hmass
  have hgI : Integrable (g : Vec d → ℝ) μ :=
    memLp_one_iff_integrable.mp (hg.trans_lt ENNReal.ofReal_lt_top)
  have hgF : (∫ x, |(g : Lp ℝ 2 μ) x| ∂μ) ≤ F := by
    have he : ENNReal.ofReal (∫ x, |(g : Lp ℝ 2 μ) x| ∂μ) ≤ ENNReal.ofReal F := by
      rw [eLpNorm_one_eq_lintegral_enorm hgI.aestronglyMeasurable,
        ← ofReal_integral_norm_eq_lintegral_enorm hgI] at hg
      simpa only [Real.norm_eq_abs] using hg
    exact (ENNReal.ofReal_le_ofReal_iff hF.le).mp he
  exact hN g hgI F hF hgF t ht

/-- The unforced physical evolution maps spatial L¹ data to L² with Nash decay. -/
theorem u7_unforced_physical_L1_to_L2
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0), 0 < t →
      ∀ (g : Vec d → ℝ) (hg1 : Integrable g volume)
        (hg2 : MemLp g 2 (physicalReversibleMeasure ω hd 0)),
      ‖Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω t (hg2.toLp g)‖ ≤
        C * (t : ℝ) ^ (-(d : ℝ) / 4) * ∫ y, |g y| := by
  obtain ⟨C, hC, hdec⟩ := u7_unforced_physical_L1_L2_decay hd ω Λ hΛ hω
  let μ := physicalReversibleMeasure ω hd 0
  let K := Real.exp (2 * Λ)
  let A : ℝ := 4 / ((d : ℝ) * C ^ (1 + 2 / (d : ℝ)))
  have hdR : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hd)
  have hK : 0 < K := Real.exp_pos _
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨A ^ (-(d : ℝ) / 4) * K, by positivity, ?_⟩
  intro t ht g hg1 hg2
  have htR : (0 : ℝ) < t := ht
  have hgμ : Integrable g μ := memLp_one_iff_integrable.mp <|
    (memLp_one_iff_integrable.mpr hg1).of_measure_le_smul
      (c := ENNReal.ofReal K) ENNReal.ofReal_ne_top
      (u4_unforced_physical_measure_comparable hd ω Λ hω).1
  have hmass : (∫ x, |g x| ∂μ) ≤ K * (∫ x, |g x|) := by
    apply integral_le_const_mul_of_measure_le μ volume K hK.le
      (u4_unforced_physical_measure_comparable hd ω Λ hω).1
      (fun x => |g x|) (Filter.Eventually.of_forall fun x => abs_nonneg _)
    simpa only [Real.norm_eq_abs] using hg1.norm
  let f : Lp ℝ 2 μ := hg2.toLp g
  have hf : Integrable f μ := hgμ.congr hg2.coeFn_toLp.symm
  have hmassf : (∫ x, |f x| ∂μ) ≤ K * (∫ x, |g x|) := by
    convert hmass using 1
    apply integral_congr_ae
    filter_upwards [hg2.coeFn_toLp] with x hx
    change f x = g x at hx
    simp only [hx]
  let F : ℝ := ∫ x, |f x| ∂μ
  have hF : 0 ≤ F := integral_nonneg fun _ => abs_nonneg _
  by_cases hz : F = 0
  · have hae : ∀ᵐ x ∂μ, |f x| = 0 :=
      (integral_eq_zero_iff_of_nonneg (fun _ => abs_nonneg _) (by
        simpa only [Real.norm_eq_abs] using hf.norm)).mp hz
    have hf0 : f = 0 := by
      apply Lp.ext
      filter_upwards [hae, Lp.coeFn_zero (E := ℝ) (p := 2) (μ := μ)] with x hx hz
      rw [hz]
      exact abs_eq_zero.mp hx
    change ‖Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω t f‖ ≤ _
    rw [hf0, map_zero, norm_zero]
    positivity
  have hFp : 0 < F := lt_of_le_of_ne hF (Ne.symm hz)
  have hb := hdec f hf F hFp le_rfl t ht
  have hp : -(4 / (d : ℝ)) * (-(d : ℝ) / 2) = (2 : ℝ) := by field_simp; ring
  have he : (4 / ((d : ℝ) * C ^ (1 + 2 / (d : ℝ)) * F ^ (4 / (d : ℝ)))) * t =
      (A * t) * F ^ (-(4 / (d : ℝ))) := by
    rw [Real.rpow_neg hFp.le]
    dsimp [A]
    ring
  rw [he, Real.mul_rpow (mul_nonneg hA.le htR.le) (Real.rpow_nonneg hFp.le _),
    ← Real.rpow_mul hFp.le, hp, Real.rpow_two] at hb
  have hp2 : (-(d : ℝ) / 4) * 2 = -(d : ℝ) / 2 := by ring
  have hsq : (A ^ (-(d : ℝ) / 4) * (t : ℝ) ^ (-(d : ℝ) / 4) * F) ^ 2 =
      (A * t) ^ (-(d : ℝ) / 2) * F ^ 2 := by
    rw [Real.mul_rpow hA.le htR.le, mul_pow, mul_pow]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hA.le]
    norm_num only [Nat.cast_ofNat]
    rw [hp2, ← Real.rpow_natCast, ← Real.rpow_mul htR.le]
    norm_num only [Nat.cast_ofNat]
    rw [hp2]
  have hnorm : ‖Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω t f‖ ≤
      A ^ (-(d : ℝ) / 4) * (t : ℝ) ^ (-(d : ℝ) / 4) * F := by
    have hn : 0 ≤ A ^ (-(d : ℝ) / 4) * (t : ℝ) ^ (-(d : ℝ) / 4) * F := by positivity
    rw [← hsq] at hb
    nlinarith [norm_nonneg (Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω t f)]
  calc
    _ ≤ A ^ (-(d : ℝ) / 4) * (t : ℝ) ^ (-(d : ℝ) / 4) * F := hnorm
    _ ≤ A ^ (-(d : ℝ) / 4) * (t : ℝ) ^ (-(d : ℝ) / 4) * (K * ∫ x, |g x|) := by gcongr
    _ = _ := by ring

#print axioms u7_unforced_physical_L1_to_L2

#print axioms u7_unforced_physical_L1_L2_decay
#print axioms u7_unforced_physical_generator_orbit_nash
#print axioms u7_nash_raise
#print axioms u7_unforced_physical_generator_decay

end EinsteinFull
