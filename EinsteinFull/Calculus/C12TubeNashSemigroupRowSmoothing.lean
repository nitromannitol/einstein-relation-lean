import EinsteinFull.Calculus.C12TubeWeightedNash
import SubdiffusiveProcess.Nash.Decay

open MeasureTheory PDE EinsteinFull.External.Source.GMP
open EinsteinRelation
open EinsteinFull.Blueprint.TubeProbability
open EinsteinFull.Blueprint.TubeProbability.DimensionLift
open EinsteinFull.Blueprint.SbxS3UniformCrossHeat
open scoped ENNReal NNReal

noncomputable section
namespace EinsteinFull.Calculus

/-- A symmetric submarkovian operator on a finite measure space contracts the
integral of the absolute value on its native L² space. -/
theorem finite_symmetric_submarkov_L1_contraction {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (P : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hpos : ∀ f : Lp ℝ 2 μ, (∀ᵐ x ∂μ, 0 ≤ f x) → ∀ᵐ x ∂μ, 0 ≤ P f x)
    (hunit : ∀ f : Lp ℝ 2 μ, (∀ᵐ x ∂μ, 0 ≤ f x ∧ f x ≤ 1) →
      ∀ᵐ x ∂μ, 0 ≤ P f x ∧ P f x ≤ 1)
    (hsym : ∀ f g, inner ℝ (P f) g = inner ℝ f (P g))
    (f : Lp ℝ 2 μ) :
    (∫ x, |P f x| ∂μ) ≤ ∫ x, |f x| ∂μ := by
  let one : Lp ℝ 2 μ := Lp.const 2 μ (1 : ℝ)
  have hone : ∀ᵐ x ∂μ, 0 ≤ one x ∧ one x ≤ 1 := by
    filter_upwards [Lp.coeFn_const (μ := μ) (p := 2) (c := (1 : ℝ))] with x hx
    rw [show one x = 1 from hx]
    exact ⟨zero_le_one, le_rfl⟩
  have hpone := hunit one hone
  have hmono (f g : Lp ℝ 2 μ) (hfg : f ≤ g) : P f ≤ P g := by
    apply sub_nonneg.mp
    rw [← map_sub]
    exact (Lp.coeFn_nonneg _).1 (hpos _ ((Lp.coeFn_nonneg _).2 (sub_nonneg.mpr hfg)))
  have habs : |P f| ≤ P |f| := by
    apply abs_le'.2
    constructor
    · exact hmono _ _ (le_abs_self f)
    · simpa only [map_neg] using hmono _ _ (neg_le_abs f)
  have ha : ∀ᵐ x ∂μ, |P f x| ≤ P |f| x := by
    filter_upwards [(Lp.coeFn_le _ _).2 habs, Lp.coeFn_abs (P f)] with x hx he
    simpa only [he] using hx
  have hint (g : Lp ℝ 2 μ) : Integrable g μ := by
    simpa only [integrableOn_univ] using
      (integrableOn_Lp_of_measure_ne_top g (by norm_num) (measure_ne_top μ Set.univ))
  have hi : Integrable (fun x => P one x * |f x|) μ := by
    apply Integrable.congr (L2.integrable_inner (𝕜 := ℝ) (P one) |f|)
    filter_upwards [Lp.coeFn_abs f] with x hx
    simp only [Real.inner_apply, hx]
  have hle : (∫ x, P one x * |f x| ∂μ) ≤ ∫ x, |f x| ∂μ := by
    apply integral_mono_ae hi (hint f).abs
    filter_upwards [hpone] with x hx
    nlinarith [mul_nonneg (sub_nonneg.mpr hx.2) (abs_nonneg (f x))]
  calc
    _ ≤ ∫ x, P |f| x ∂μ := integral_mono_ae (hint (P f)).abs (hint (P |f|)) ha
    _ = inner ℝ (P |f|) one := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_const (μ := μ) (p := 2) (c := (1 : ℝ))] with x hx
      rw [Real.inner_apply, show one x = 1 from hx]
      simp
    _ = inner ℝ |f| (P one) := hsym _ _
    _ = ∫ x, P one x * |f x| ∂μ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_abs f] with x hx
      simp only [Real.inner_apply, hx, mul_comm]
    _ ≤ _ := hle

/-- The native weighted Dirichlet spectral heat operator contracts L¹. -/
theorem dirichletHilbert_spectralHeat_L1_contraction {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (R : ℝ) (hR : 0 < R)
    (eigenvalue : ℕ → ℝ) (hpos : ∀ n, 0 ≤ eigenvalue n)
    (vs : ℕ → DirichletHilbertSpace (d := d) R hR)
    (b : HilbertBasis ℕ ℝ (Lp ℝ 2 (dirichletVolume ρ R)))
    (hb : ∀ n, b n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (vs n))
    (hvarb : ∀ n, ∀ w : DirichletHilbertSpace (d := d) R hR,
      (∫ x in sourceBall (0 : PDE.Vec d) R,
        dot ((α x).mulVec (fun i => (vs n).val (some i) x))
          (fun i => w.val (some i) x)) =
      eigenvalue n * inner ℝ (b n) (dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) w))
    (t : ℝ≥0) (f : Lp ℝ 2 (dirichletVolume ρ R)) :
    (∫ x, |SpectralHeat.heatOperator b eigenvalue hpos t f x| ∂dirichletVolume ρ R) ≤
      ∫ x, |f x| ∂dirichletVolume ρ R := by
  have : IsFiniteMeasure (dirichletVolume ρ R) :=
    dirichletVolume_isFinite ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  apply finite_symmetric_submarkov_L1_contraction (dirichletVolume ρ R)
    (SpectralHeat.heatOperator b eigenvalue hpos t)
  · intro g hg
    exact (dirichletHilbert_spectralHeat_order hd hκ h R hR eigenvalue hpos vs b hb hvarb t g).1 hg
  · intro g hg
    exact (dirichletHilbert_spectralHeat_order hd hκ h R hR eigenvalue hpos vs b hb hvarb t g).2 hg
  · exact SpectralHeat.heatOperator_symmetric b eigenvalue hpos t

#print axioms dirichletHilbert_spectralHeat_L1_contraction

/-- The weighted Nash inequality expressed in the native weighted L² carrier. -/
theorem dirichletHilbert_weighted_nash_inclusion {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ) (hR : 0 < R)
      (ρ : PDE.Vec d → ℝ) (α : PDE.Vec d → EinsteinRelation.Mat d)
      (h : IsUniformlyElliptic κ ρ α) (u : DirichletHilbertSpace (d := d) R hR),
      let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
      ‖J u‖ ^ 2 ≤ C * (∫ x in sourceBall (0 : PDE.Vec d) R,
        dot ((α x).mulVec (fun i => u.val (some i) x))
          (fun i => u.val (some i) x)) ^ ((d : ℝ) / (d + 2)) *
        (∫ x, |J u x| ∂dirichletVolume ρ R) ^ ((4 : ℝ) / (d + 2)) := by
  obtain ⟨C, hC, hn⟩ := dirichletHilbert_weighted_nash hd hκ
  refine ⟨C, hC, ?_⟩
  intro R hR ρ α h u
  dsimp only
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  have hJ : (J u : PDE.Vec d → ℝ) =ᵐ[dirichletVolume ρ R] (fun x => u.val none x) :=
    dirichletHilbertInclusion_coe ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) u
  have hsq : ‖J u‖ ^ 2 = ∫ x in sourceBall (0 : PDE.Vec d) R, ρ x * (u.val none x) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, dirichletVolume_inner_eq_native hκ h R (J u) (J u)
      (fun x => u.val none x) (fun x => u.val none x) hJ hJ]
    apply integral_congr_ae
    filter_upwards with x
    ring
  have habs : (∫ x, |J u x| ∂dirichletVolume ρ R) =
      ∫ x in sourceBall (0 : PDE.Vec d) R, ρ x * |u.val none x| := by
    calc
      _ = ∫ x, |u.val none x| ∂dirichletVolume ρ R := by
        apply integral_congr_ae
        filter_upwards [hJ] with x hx
        rw [hx]
      _ = _ := by
        change (∫ x, |u.val none x| ∂(volume.restrict (sourceBall (0 : PDE.Vec d) R)).withDensity
          (fun x => ENNReal.ofReal (ρ x))) = _
        rw [integral_withDensity_eq_integral_toReal_smul h.1.ennreal_ofReal
          (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
        apply integral_congr_ae
        filter_upwards with x
        simp only [ENNReal.toReal_ofReal (hκ.le.trans (h.2.2 x).1), smul_eq_mul]
  change ‖J u‖ ^ 2 ≤ _
  rw [hsq, habs]
  exact hn R hR ρ α h u

#print axioms dirichletHilbert_weighted_nash_inclusion

/-- The same native spectral heat flow has the Dirichlet energy as the
negative half derivative of its squared weighted L² norm. -/
theorem spectral_heat_native_energy_evolution {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : PDE.Vec d → ℝ} {α : PDE.Vec d → EinsteinRelation.Mat d}
    (h : IsUniformlyElliptic κ ρ α) (s : DirichletSpectralResolution ρ α R)
    (vs : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (vs n))
    (hvar : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (vs n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (spectralHeatBasis s n)
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w)) :
    let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
    ∃ Q : (t : ℝ≥0) → 0 < t →
      Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ] DirichletHilbertSpace (d := d) R hR,
      ∀ t ht,
        J.comp (Q t ht) = SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
          (fun n => (s.eigenvalue_pos n).le) t ∧
        ∀ f, HasDerivAt
          (fun r : ℝ => ‖SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
            (fun n => (s.eigenvalue_pos n).le) r.toNNReal f‖ ^ 2)
          (-2 * (∫ x in sourceBall (0 : PDE.Vec d) R,
            dot ((α x).mulVec (fun i => (Q t ht f).val (some i) x))
              (fun i => (Q t ht f).val (some i) x))) (t : ℝ) := by
  dsimp only
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  have hv : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (vs n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ (J (vs n)) (J w) := by
    intro n w
    simpa only [hb n] using hvar n w
  obtain ⟨Q, _, hQ⟩ := spectral_heat_native_lift hd hκ h R hR s vs hb hv
  refine ⟨Q, ?_⟩
  intro t ht
  obtain ⟨hfactor, hform, _⟩ := hQ t ht
  refine ⟨hfactor, ?_⟩
  intro f
  have hnorm := (SpectralHeat.heatOperator_hasDerivAt (spectralHeatBasis s)
    s.eigenvalue s.eigenvalue_pos t ht f).norm_sq
  have hJ : J (Q t ht f) = SpectralHeat.heatOperator (spectralHeatBasis s)
      s.eigenvalue (fun n => (s.eigenvalue_pos n).le) t f :=
    congrArg (fun T : _ →L[ℝ] _ => T f) hfactor
  have hi : inner ℝ
      (SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
        (fun n => (s.eigenvalue_pos n).le) t f)
      (SpectralHeat.firstMoment (spectralHeatBasis s) s.eigenvalue s.eigenvalue_pos t ht f) =
      (∫ x in sourceBall (0 : PDE.Vec d) R,
        dot ((α x).mulVec (fun i => (Q t ht f).val (some i) x))
          (fun i => (Q t ht f).val (some i) x)) := by
    rw [real_inner_comm, ← hJ]
    exact (hform f (Q t ht f)).symm
  simpa only [Real.toNNReal_coe, inner_neg_right, hi, mul_neg, neg_mul] using hnorm

#print axioms spectral_heat_native_energy_evolution

/-- Native heat energy evolution and its Nash bound, with the initial L¹
mass and a constant independent of the coefficient fields and radius. -/
theorem spectral_heat_native_nash_evolution {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ) (hR : 0 < R)
      (ρ : PDE.Vec d → ℝ) (α : PDE.Vec d → EinsteinRelation.Mat d)
      (h : IsUniformlyElliptic κ ρ α) (s : DirichletSpectralResolution ρ α R)
      (vs : ℕ → DirichletHilbertSpace (d := d) R hR),
      (∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) (vs n)) →
      (∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
        dot ((α x).mulVec (fun i => (vs n).val (some i) x))
          (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
        (spectralHeatBasis s n)
        (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w)) →
      let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
      ∃ Q : (t : ℝ≥0) → 0 < t →
        Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ] DirichletHilbertSpace (d := d) R hR,
        ∀ t ht f,
          J (Q t ht f) = SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
            (fun n => (s.eigenvalue_pos n).le) t f ∧
          HasDerivAt
            (fun r : ℝ => ‖SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
              (fun n => (s.eigenvalue_pos n).le) r.toNNReal f‖ ^ 2)
            (-2 * (∫ x in sourceBall (0 : PDE.Vec d) R,
              dot ((α x).mulVec (fun i => (Q t ht f).val (some i) x))
                (fun i => (Q t ht f).val (some i) x))) (t : ℝ) ∧
          ‖J (Q t ht f)‖ ^ 2 ≤ C * (∫ x in sourceBall (0 : PDE.Vec d) R,
            dot ((α x).mulVec (fun i => (Q t ht f).val (some i) x))
              (fun i => (Q t ht f).val (some i) x)) ^ ((d : ℝ) / (d + 2)) *
            (∫ x, |f x| ∂dirichletVolume ρ R) ^ ((4 : ℝ) / (d + 2)) := by
  obtain ⟨C, hC, hn⟩ := dirichletHilbert_weighted_nash_inclusion hd hκ
  refine ⟨C, hC, ?_⟩
  intro R hR ρ α h s vs hb hvar
  dsimp only
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  obtain ⟨Q, hQ⟩ := spectral_heat_native_energy_evolution hd hκ hR h s vs hb hvar
  refine ⟨Q, ?_⟩
  intro t ht f
  obtain ⟨hf, he⟩ := hQ t ht
  have hJ : J (Q t ht f) = SpectralHeat.heatOperator (spectralHeatBasis s)
      s.eigenvalue (fun n => (s.eigenvalue_pos n).le) t f :=
    congrArg (fun T : _ →L[ℝ] _ => T f) hf
  refine ⟨hJ, he f, ?_⟩
  have hcon := dirichletHilbert_spectralHeat_L1_contraction hd hκ h R hR
    s.eigenvalue (fun n => (s.eigenvalue_pos n).le) vs (spectralHeatBasis s) hb hvar t f
  have hnonneg : 0 ≤ ∫ x, |J (Q t ht f) x| ∂dirichletVolume ρ R :=
    integral_nonneg fun x => abs_nonneg _
  have hpow := Real.rpow_le_rpow hnonneg (by simpa only [hJ] using hcon)
    (show 0 ≤ (4 : ℝ) / (d + 2) by positivity)
  have henergy0 : 0 ≤ ∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (Q t ht f).val (some i) x))
        (fun i => (Q t ht f).val (some i) x) :=
    (mul_nonneg hκ.le (integral_nonneg fun x => sq_nonneg _)).trans
      (dirichletHilbert_weighted_comparisons hκ h R hR (Q t ht f)).2.2
  exact (hn R hR ρ α h (Q t ht f)).trans
    (mul_le_mul_of_nonneg_left hpow (mul_nonneg hC.le (Real.rpow_nonneg henergy0 _)))

#print axioms spectral_heat_native_nash_evolution

/-- Raising the Nash inequality isolates the energy. -/
theorem spectral_nash_raise (d C A E M : ℝ) (hd : 0 < d) (hC : 0 ≤ C)
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

/-- Integrate a Nash energy inequality along a decreasing squared-norm orbit. -/
theorem spectral_nash_scalar_decay (d C F t : ℝ) (u E : ℝ → ℝ)
    (hd : 0 < d) (hC : 0 < C) (hF : 0 < F) (ht : 0 < t)
    (hu : ContinuousOn u (Set.Icc 0 t)) (hu0 : ∀ s, 0 ≤ u s)
    (hanti : Antitone u)
    (hE : ∀ s ∈ Set.Ioo 0 t, 0 ≤ E s)
    (hder : ∀ s ∈ Set.Ioo 0 t, HasDerivAt u (-2 * E s) s)
    (hnash : ∀ s ∈ Set.Ioo 0 t,
      u s ≤ C * E s ^ (d / (d + 2)) * F ^ (4 / (d + 2))) :
    u t ≤ ((4 / (d * C ^ (1 + 2 / d) * F ^ (4 / d))) * t) ^ (-d / 2) := by
  let K : ℝ := C ^ (1 + 2 / d) * F ^ (4 / d)
  have hK : 0 < K := by dsimp [K]; positivity
  let c : ℝ := 4 / (d * K)
  have hc : 0 < c := by dsimp [c]; positivity
  by_cases hut : u t = 0
  · rw [hut]; positivity
  have hutP : 0 < u t := lt_of_le_of_ne (hu0 t) (Ne.symm hut)
  have hpos (s : ℝ) (hs : s ∈ Set.Icc 0 t) : 0 < u s :=
    hutP.trans_le (hanti hs.2)
  have hineq (s : ℝ) (hs : s ∈ Set.Ioo 0 t) :
      -2 * E s ≤ -((d / 2) * c) * u s ^ (1 + 1 / (d / 2)) := by
    have hraised := spectral_nash_raise d C (u s) (E s) F hd hC.le
      (hu0 s) (hE s hs) hF.le (hnash s hs)
    have hbound : u s ^ (1 + 2 / d) ≤ K * E s := by
      calc
        _ ≤ C ^ (1 + 2 / d) * E s * F ^ (4 / d) := hraised
        _ = K * E s := by dsimp [K]; ring
    have he : u s ^ (1 + 2 / d) / K ≤ E s :=
      (div_le_iff₀ hK).2 (by simpa [mul_comm] using hbound)
    calc
      -2 * E s ≤ -2 * (u s ^ (1 + 2 / d) / K) :=
        mul_le_mul_of_nonpos_left he (by norm_num)
      _ = -((d / 2) * c) * u s ^ (1 + 1 / (d / 2)) := by
        have hex : 1 + 1 / (d / 2) = 1 + 2 / d := by field_simp
        rw [hex]
        dsimp [c]
        field_simp [ne_of_gt hd, ne_of_gt hK] <;> ring
  have hdec := SubdiffusiveProcess.Nash.decay_rpow u (fun s => -2 * E s)
    (d / 2) c t (by positivity) hc ht hu hpos hder hineq
  simpa only [c, K, mul_assoc, neg_div] using hdec

#print axioms spectral_nash_scalar_decay

/-- Structural L¹-to-L² decay for the native spectral heat operator. -/
theorem spectral_heat_native_L1_L2_decay {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (R : ℝ) (hR : 0 < R)
      (ρ : PDE.Vec d → ℝ) (α : PDE.Vec d → EinsteinRelation.Mat d)
      (h : IsUniformlyElliptic κ ρ α) (s : DirichletSpectralResolution ρ α R)
      (vs : ℕ → DirichletHilbertSpace (d := d) R hR),
      (∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) (vs n)) →
      (∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
        dot ((α x).mulVec (fun i => (vs n).val (some i) x))
          (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
        (spectralHeatBasis s n)
        (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w)) →
      ∀ (f : Lp ℝ 2 (dirichletVolume ρ R)) (F : ℝ),
        0 < F → (∫ x, |f x| ∂dirichletVolume ρ R) ≤ F →
      ∀ (t : ℝ≥0), 0 < t →
        ‖SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
          (fun n => (s.eigenvalue_pos n).le) t f‖ ^ 2 ≤
        ((4 / ((d : ℝ) * C ^ (1 + 2 / (d : ℝ)) * F ^ (4 / (d : ℝ)))) * t) ^
          (-(d : ℝ) / 2) := by
  obtain ⟨C, hC, hN⟩ := spectral_heat_native_nash_evolution hd hκ
  refine ⟨C, hC, ?_⟩
  intro R hR ρ α h s vs hb hvar f F hF hfF t ht
  obtain ⟨Q, hQ⟩ := hN R hR ρ α h s vs hb hvar
  let P := SpectralHeat.heatOperator (spectralHeatBasis s) s.eigenvalue
    (fun n => (s.eigenvalue_pos n).le)
  let u : ℝ → ℝ := fun r => ‖P r.toNNReal f‖ ^ 2
  let E : ℝ → ℝ := fun r => if hr : 0 < r then
    ∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (Q r.toNNReal (Real.toNNReal_pos.mpr hr) f).val (some i) x))
        (fun i => (Q r.toNNReal (Real.toNNReal_pos.mpr hr) f).val (some i) x)
    else 0
  have hdR : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hd)
  have ha : Antitone u := by
    intro a b hab
    have hab' : a.toNNReal ≤ b.toNNReal := Real.toNNReal_mono hab
    have hp : ‖P b.toNNReal f‖ ≤ ‖P a.toNNReal f‖ := by
      rw [← add_tsub_cancel_of_le hab', add_comm a.toNNReal (b.toNNReal - a.toNNReal)]
      dsimp [P]
      rw [SpectralHeat.heatOperator_add, ContinuousLinearMap.comp_apply]
      exact SpectralHeat.heatOperator_norm_le _ _ _ _ _
    exact pow_le_pow_left₀ (norm_nonneg _) hp 2
  have hE (r : ℝ) (hr : r ∈ Set.Ioo 0 (t : ℝ)) : 0 ≤ E r := by
    simp only [E, dif_pos hr.1]
    exact (mul_nonneg hκ.le (integral_nonneg fun x => sq_nonneg _)).trans
      (dirichletHilbert_weighted_comparisons hκ h R hR
        (Q r.toNNReal (Real.toNNReal_pos.mpr hr.1) f)).2.2
  have hder (r : ℝ) (hr : r ∈ Set.Ioo 0 (t : ℝ)) : HasDerivAt u (-2 * E r) r := by
    have hr' : 0 < r.toNNReal := Real.toNNReal_pos.mpr hr.1
    have hh := (hQ r.toNNReal hr' f).2.1
    simpa [u, P, E, hr.1, Real.coe_toNNReal _ hr.1.le] using hh
  have hnash (r : ℝ) (hr : r ∈ Set.Ioo 0 (t : ℝ)) :
      u r ≤ C * E r ^ ((d : ℝ) / (d + 2)) * F ^ (4 / ((d : ℝ) + 2)) := by
    have hr' : 0 < r.toNNReal := Real.toNNReal_pos.mpr hr.1
    have hh := (hQ r.toNNReal hr' f)
    have hm : 0 ≤ ∫ x, |f x| ∂dirichletVolume ρ R := integral_nonneg fun _ => abs_nonneg _
    have hmass := Real.rpow_le_rpow hm hfF (show 0 ≤ (4 : ℝ) / ((d : ℝ) + 2) by positivity)
    have hn : u r ≤ C * E r ^ ((d : ℝ) / (d + 2)) *
        (∫ x, |f x| ∂dirichletVolume ρ R) ^ (4 / ((d : ℝ) + 2)) := by
      simpa [u, P, E, hr.1, hh.1] using hh.2.2
    exact hn.trans (mul_le_mul_of_nonneg_left hmass
      (mul_nonneg hC.le (Real.rpow_nonneg (hE r hr) _)))
  have hc : ContinuousOn u (Set.Icc 0 (t : ℝ)) := by
    apply Continuous.continuousOn
    exact (((SpectralHeat.heatOperator_continuous _ _ _ f).comp
      continuous_real_toNNReal).norm.pow 2)
  have hdec := spectral_nash_scalar_decay (d : ℝ) C F t u E hdR hC hF ht
    hc (fun r => sq_nonneg _) ha hE hder hnash
  simpa [u, P] using hdec

#print axioms spectral_heat_native_L1_L2_decay

/-- A native positive-time spectral row has weighted L¹ mass at most one. -/
theorem spectral_heat_native_row_L1_le_one {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) {ρ : PDE.Vec d → ℝ}
    {α : PDE.Vec d → EinsteinRelation.Mat d} (h : IsUniformlyElliptic κ ρ α)
    (R : ℝ) (hR : 0 < R) (s : DirichletSpectralResolution ρ α R)
    (vs : ℕ → DirichletHilbertSpace (d := d) R hR)
    (hs : Filter.Tendsto s.eigenvalue Filter.atTop Filter.atTop)
    (hb : ∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
      (fun x _ => (h.2.2 x).2.1) (vs n))
    (hvar : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (vs n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (spectralHeatBasis s n)
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w))
    (t : ℝ≥0) (ht : 0 < t) (x : PDE.Vec d) (hx : x ∈ sourceBall 0 R) :
    (∫ y, |spectralHeatRow s t x y| ∂dirichletVolume ρ R) ≤ 1 := by
  haveI : IsFiniteMeasure (dirichletVolume ρ R) :=
    dirichletVolume_isFinite ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1)
  have hv : ∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
      dot ((α x).mulVec (fun i => (vs n).val (some i) x))
        (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) (vs n))
      (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w) := by
    intro n w
    rw [← hb n]
    exact hvar n w
  have hk := spectral_heat_kernel_nonneg_of_variational hd hκ h R hR s hs vs hb hv
  let one : Lp ℝ 2 (dirichletVolume ρ R) := Lp.const 2 _ (1 : ℝ)
  have hone : ∀ᵐ y ∂dirichletVolume ρ R, 0 ≤ one y ∧ one y ≤ 1 := by
    filter_upwards [Lp.coeFn_const (μ := dirichletVolume ρ R) (p := 2) (c := (1 : ℝ))] with y hy
    simp only [one, Function.const_apply] at hy
    rw [hy]
    exact ⟨zero_le_one, le_rfl⟩
  have hm := (hk.1 t (by exact_mod_cast ht) one hone x hx).2
  have hball : ∀ᵐ y ∂dirichletVolume ρ R, y ∈ sourceBall 0 R := by
    have hmeas : MeasurableSet (sourceBall (0 : PDE.Vec d) R) := by
      rw [← pde_ball_eq_sourceBall _ hR]
      exact (PDE.isOpen_euclideanBall _ _).measurableSet
    exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hmeas)
  have heq : (∫ y, |spectralHeatRow s t x y| ∂dirichletVolume ρ R) =
      ∫ y, (∑' i, Real.exp (-s.eigenvalue i * (t : ℝ)) *
        s.eigenfunction i x * s.eigenfunction i y) * one y ∂dirichletVolume ρ R := by
    apply integral_congr_ae
    filter_upwards [spectral_heat_row_Lp_ae_eq_closedBall hd hκ h hR s t
      (by exact_mod_cast ht) x (subset_closure hx), hball,
      Lp.coeFn_const (μ := dirichletVolume ρ R) (p := 2) (c := (1 : ℝ))] with y hy hyball hone
    have hp := hk.2 t (by exact_mod_cast ht) x hx y hyball
    simp only [one, Function.const_apply] at hone
    rw [hy, abs_of_nonneg hp, hone, mul_one]
  rw [heq]
  exact hm

#print axioms spectral_heat_native_row_L1_le_one

/-- Time-one heat rows have a structural bound on the entire source ball. -/
theorem spectral_heat_native_row_time_one_bound {d : ℕ} (hd : 2 ≤ d)
    {κ : ℝ} (hκ : 0 < κ) (R : ℝ) (hR : 0 < R) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (ρ : PDE.Vec d → ℝ)
      (α : PDE.Vec d → EinsteinRelation.Mat d) (h : IsUniformlyElliptic κ ρ α)
      (s : DirichletSpectralResolution ρ α R)
      (vs : ℕ → DirichletHilbertSpace (d := d) R hR),
      Filter.Tendsto s.eigenvalue Filter.atTop Filter.atTop →
      (∀ n, spectralHeatBasis s n = dirichletHilbertInclusion ρ R hR κ⁻¹
        (fun x _ => (h.2.2 x).2.1) (vs n)) →
      (∀ n w, (∫ x in sourceBall (0 : PDE.Vec d) R,
        dot ((α x).mulVec (fun i => (vs n).val (some i) x))
          (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
        (spectralHeatBasis s n)
        (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (h.2.2 x).2.1) w)) →
      ∀ x ∈ sourceBall 0 R, ‖spectralHeatRow s 1 x‖ ≤ C₀ := by
  obtain ⟨C, hC, hdec⟩ := spectral_heat_native_L1_L2_decay hd hκ
  let B : ℝ := ((4 / ((d : ℝ) * C ^ (1 + 2 / (d : ℝ)) * (1 : ℝ) ^ (4 / (d : ℝ)))) *
    ((1 / 2 : ℝ≥0) : ℝ)) ^ (-(d : ℝ) / 2)
  refine ⟨Real.sqrt B, Real.sqrt_nonneg _, ?_⟩
  intro ρ α h s vs hs hb hvar x hx
  have hmass := spectral_heat_native_row_L1_le_one hd hκ h R hR s vs hs hb hvar
    (1 / 2) (by norm_num) x hx
  have hD := hdec R hR ρ α h s vs hb hvar (spectralHeatRow s (1 / 2) x)
    1 (by norm_num) hmass (1 / 2) (by norm_num)
  have hrow := spectral_heat_operator_row hd hκ h hR s (1 / 2) (1 / 2)
    (by norm_num) x hx
  rw [hrow] at hD
  norm_num at hD
  have hsq : ‖spectralHeatRow s 1 x‖ ^ 2 ≤ B := by
    simpa [B] using hD
  have hB : 0 ≤ B := by dsimp [B]; positivity
  exact (Real.le_sqrt (norm_nonneg _) hB).2 hsq

#print axioms spectral_heat_native_row_time_one_bound

end EinsteinFull.Calculus
