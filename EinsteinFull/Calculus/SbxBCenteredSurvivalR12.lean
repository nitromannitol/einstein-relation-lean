import EinsteinFull.Calculus.SbxBActualNativeLowerTransferR11
import EinsteinFull.Calculus.SbxBCappedNativeLowerR03
import EinsteinFull.Calculus.SbxBCenteredTubeChainR03
import EinsteinFull.Calculus.SbxS4KilledTranslationR02
import EinsteinFull.Calculus.U5RegularSignedRealization

open MeasureTheory
open scoped NNReal ENNReal
namespace EinsteinFull
open EinsteinRelation EinsteinRelation.Diffusion EinsteinRelation.SpatialDirichlet
open EinsteinRelation.External.GantertSection7Support
open EinsteinFull.Blueprint.TubeProbability EinsteinFull.External.Source.GMP

/-- A lower bound for the native source-normalized kernel on an endpoint ball
implies survival in the larger ball for the actual realization. -/
theorem b_centered_return_of_native_lower
    (c : ℝ) (hc : 0 < c)
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (hcoeff : ∀ x ∈ sourceBall (0 : Vec d) R,
      ρ x = s4PhysicalRho hd ω lam x ∧ α x = s4PhysicalAlpha hd ω lam x)
    {K : ℝ → Vec d → Vec d → ℝ} {G : ℝ → Vec d → Vec d → Vec d}
    (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
    (t : ℝ≥0) (ht : 0 < (t : ℝ))
    (y : Vec d) (hy : y ∈ sourceBall 0 (R/2))
    (hlower : ∀ x ∈ sourceBall (0 : Vec d) (R/2), c ≤ K t x y / ρ y) :
    ENNReal.ofReal (κ * c) * volume (sourceBall (0 : Vec d) (R/2)) ≤
      r.pathLaw y {γ : Path d | (∀ s : ℝ≥0, s ≤ t → euclideanNorm (γ s) < R) ∧
        euclideanNorm (γ t) < R/2} := by
  let V : Set (Vec d) := sourceBall 0 (R/2)
  have hV : MeasurableSet V := (Calculus.c12_sourceBall_volume (0 : Vec d) (by positivity : 0 < R/2)).1
  have hsub : V ⊆ sourceBall 0 R := by
    intro x hx
    change euclideanNorm (x - 0) < R/2 at hx
    change euclideanNorm (x - 0) < R
    linarith
  have hyR : y ∈ sourceBall 0 R := hsub hy
  let a : ℝ := Real.rpow (t : ℝ) (-(d : ℝ)/2)
  have ha : 0 < a := Real.rpow_pos_of_pos ht _
  have hla : ∀ x ∈ V, (c / a) * Real.rpow (t : ℝ) (-(d : ℝ)/2) ≤ K t x y / ρ y := by
    intro x hx
    simpa only [show (c / a) * Real.rpow (t : ℝ) (-(d : ℝ)/2) = c by
      dsimp only [a]; exact div_mul_cancel₀ c ha.ne'] using hlower x hx
  have hm := b_actual_native_setwise_lower_of_pointwise (c/a) κ (div_pos hc ha) hκ r
    hκ hR hell hcoeff hK t ht y hyR V hV hsub hla (fun x _ => (hell.2.2 x).1)
  have hs : κ * (c / a) * Real.rpow (t : ℝ) (-(d : ℝ)/2) = κ * c := by
    dsimp only [a] at *
    rw [mul_assoc, div_mul_cancel₀ c ha.ne']
  have hv := hm V
  rw [Measure.smul_apply, Measure.restrict_apply hV, Set.inter_self, hs] at hv
  rw [gmpKilledEndpointKernel_apply r (sourceBall 0 R)
      (dirichletBall (d := d) R).isOpen t y,
    Measure.map_apply (measurable_pathPosition t) hV,
    Measure.restrict_apply ((measurable_pathPosition t) hV)] at hv
  apply hv.trans
  apply measure_mono
  intro γ hγ
  refine ⟨?_, ?_⟩
  · intro s hs'
    have hsurv := (lt_localityExitTime_iff _ (dirichletBall (d := d) R).isOpen γ t).mp hγ.2 s hs'
    change euclideanNorm (γ s - 0) < R at hsurv
    simpa only [sub_zero] using hsurv
  · have hh : γ t ∈ V := hγ.1
    change euclideanNorm (γ t - 0) < R/2 at hh
    simpa only [sub_zero] using hh

/-- Uniform centered survival at the origin on the physical ball `S / μ`.
The force scale is arbitrary and the two native analytic inputs remain separate. -/
theorem b_scaled_centered_return_of_native_short_time
    (d : ℕ) (hd : 2 ≤ d) (κ δ H S T : ℝ)
    (hκ : 0 < κ) (hδ : 0 < δ) (hH : 0 < H) (hS : 0 < S) (hT : 0 < T) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
      {L : ℝ} {hL : 1 ≤ L} {ω : FieldPair d} {hω : IsRegular L ω}
      (r : GantertFixedEnvironmentRealization hd L hL ω hω μ hμ.le hμ1)
      (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
      (∀ x ∈ sourceBall (0 : Vec d) (S/μ),
        ρ x = s4PhysicalRho hd ω μ x ∧ α x = s4PhysicalAlpha hd ω μ x) →
      ∀ (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
      IsSpectralDirichletFundamentalSolution ρ α (S/μ) K G →
      (∀ (x : Vec d) (r u : ℝ), 0 < r → sourceBall x (2*r) ⊆ sourceBall 0 (S/μ) →
        0 < u → u ≤ δ*r^2 → (1/2 : ℝ) ≤ ∫ y in sourceBall 0 (S/μ), K u x y) →
      (∀ (x y : Vec d) (r u : ℝ), 0 < r → sourceBall x (2*r) ⊆ sourceBall 0 (S/μ) →
        y ∈ sourceBall 0 (S/μ) → 0 < u → u ≤ δ*r^2 → euclideanSq (x-y) ≤ u →
        K (2*u) x x / ρ x ≤ H * (K (4*u) x y / ρ y)) →
      ∀ y ∈ sourceBall 0 ((S/μ)/2),
      ENNReal.ofReal ε ≤ r.pathLaw y {γ : Path d |
        (∀ s : ℝ≥0, s ≤ (T/μ^2).toNNReal → euclideanNorm (γ s) < S/μ) ∧
        euclideanNorm (γ (T/μ^2).toNNReal) < (S/μ)/2} := by
  obtain ⟨c, hc, hbound⟩ := Calculus.b_source_oriented_capped_fixed_time_lower
    d hd κ δ H S T hκ hδ hH hS hT
  let v : ℝ := (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal
  have hv : 0 < v := by
    have h := (Calculus.c12_sourceBall_volume (0 : Vec d) (by norm_num : (0 : ℝ) < 1)).2.2
    have he := h.2
    simp only [one_pow, one_mul] at he
    dsimp only [v]
    rw [← he]
    exact h.1
  refine ⟨κ * c * ((S/2)^d * v), by positivity, ?_⟩
  intro μ hμ hμ1 L hL ω hω r ρ α hell hcoeff K G hK hmass hcompare y hy
  have hR : 0 < S/μ := div_pos hS hμ
  have ht : 0 < T/μ^2 := div_pos hT (sq_pos_of_pos hμ)
  have hscaled (x : Vec d) (hx : x ∈ sourceBall 0 ((S/μ)/2)) :
      μ • x ∈ sourceBall (0 : Vec d) (S/2) := by
    change euclideanNorm (μ • x - 0) < S/2
    simp only [sub_zero, TimeChange.euclideanNorm_smul, abs_of_pos hμ]
    change euclideanNorm (x - 0) < (S/μ)/2 at hx
    simp only [sub_zero] at hx
    have hm := mul_lt_mul_of_pos_left hx hμ
    convert hm using 1; field_simp
  have hpoint : ∀ x ∈ sourceBall (0 : Vec d) ((S/μ)/2),
      c * μ^d ≤ K (T/μ^2) x y / ρ y := by
    intro x hx
    have hh := hbound (S/μ) μ hR hμ (by field_simp) ρ α hell K G hK
      hmass hcompare (μ • y) (hscaled y hy) (μ • x) (hscaled x hx)
    simp only [smul_smul, inv_mul_cancel₀ hμ.ne', one_smul] at hh
    have hp : 0 < μ^d := pow_pos hμ _
    have hh' : c ≤ (μ^d)⁻¹ * (K (T/μ^2) x y / ρ y) := by
      simpa only [inv_pow, div_eq_mul_inv, mul_assoc] using hh
    simpa only [mul_comm] using (le_inv_mul_iff₀ hp).mp hh'
  have hsurv := b_centered_return_of_native_lower (c*μ^d) (mul_pos hc (pow_pos hμ _))
    r hκ hR hell hcoeff hK (T/μ^2).toNNReal
    (by simpa [Real.coe_toNNReal _ ht.le] using ht) y hy
    (by simpa only [Real.coe_toNNReal _ ht.le] using hpoint)
  have hvol := Calculus.c12_sourceBall_volume (0 : Vec d) (by positivity : 0 < (S/μ)/2)
  have heq : κ * c * ((S/2)^d * v) =
      (κ * (c*μ^d)) * (volume (sourceBall (0 : Vec d) ((S/μ)/2))).toReal := by
    rw [hvol.2.2.2]
    dsimp only [v]
    have hr : ((S/μ)/2)^d = (S/2)^d / μ^d := by
      rw [show (S/μ)/2 = (S/2)/μ by ring, div_pow]
    rw [hr]
    have hp : μ^d ≠ 0 := pow_ne_zero _ hμ.ne'
    calc
      _ = κ * c * ((μ^d * ((S/2)^d / μ^d)) *
          (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal) := by
        rw [mul_div_cancel₀ _ hp]
      _ = _ := by ring
  rw [heq, ENNReal.ofReal_mul (mul_nonneg hκ.le (mul_nonneg hc.le (pow_nonneg hμ.le _))),
    ENNReal.ofReal_toReal hvol.2.1]
  exact hsurv


/-- Translation of the strict killed-return event for actual realizations. -/
theorem b_centered_return_of_translated_environment
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L)
    (ω : FieldPair d) (hω : IsRegular L ω) (μ : ℝ) (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (c : Vec d) (hωc : IsRegular L (translate c ω))
    (r : GantertFixedEnvironmentRealization hd L hL ω hω μ hμ hμ1)
    (r' : GantertFixedEnvironmentRealization hd L hL (translate c ω) hωc μ hμ hμ1)
    (y : Vec d) (t : ℝ≥0) (R : ℝ) :
    r'.pathLaw (y-c) {γ : Path d |
      (∀ s : ℝ≥0, s ≤ t → euclideanNorm (γ s) < R) ∧ euclideanNorm (γ t) < R/2} =
    r.pathLaw y {γ : Path d |
      (∀ s : ℝ≥0, s ≤ t → euclideanNorm (γ s - c) < R) ∧
      euclideanNorm (γ t - c) < R/2} := by
  have hr := funext (u6_arbitrary_supplied_gmp_transition_eq hd ω μ L hL hω hμ hμ1 r)
  have hr' := funext (u6_arbitrary_supplied_gmp_transition_eq hd (translate c ω) μ L hL hωc hμ hμ1 r')
  have hp := s2_regular_realization_path_translation hd L hL ω hω μ hμ hμ1 c hωc r r' hr hr' (y-c)
  have he : y-c+c = y := by abel
  rw [he] at hp
  rw [hp]
  let A : Set (Path d) := {γ | (∀ s : ℝ≥0, s ≤ t → euclideanNorm (γ s) < R) ∧
    euclideanNorm (γ t) < R/2}
  have hA : MeasurableSet A := by
    have heq : A = {γ : Path d | (t : ℝ≥0∞) < localityExitTime (sourceBall 0 R) γ} ∩
        pathPosition t ⁻¹' sourceBall 0 (R/2) := by
      ext γ
      simp only [A, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]
      rw [lt_localityExitTime_iff (sourceBall 0 R) (dirichletBall (d := d) R).isOpen γ t]
      simp [sourceBall, pathPosition]
    rw [heq]
    exact (measurableSet_localitySurvival _ (dirichletBall (d := d) R).isOpen t).inter
      ((dirichletBall (d := d) (R/2)).isOpen.measurableSet.preimage (measurable_pathPosition t))
  rw [Measure.map_apply (Regeneration.recenterPathEquiv c).measurable hA]
  congr 1

/-- Existence of a spectral kernel matching the physical coefficients on the
scaled ball, with the displayed uniform ellipticity constant. -/
@[nolint defsWithUnderscore]
def b_native_spectral_input (d : ℕ) (hd : 2 ≤ d) (L l κ : ℝ) : Prop :=
  ∀ (ω : FieldPair d), IsRegular (sourceReducedBound L) ω → ∀ (μ : ℝ), 0 < μ → μ ≤ 1 →
    ∃ (ρ : Vec d → ℝ) (α : Vec d → Mat d)
      (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
      IsUniformlyElliptic κ ρ α ∧
      (∀ x ∈ sourceBall (0 : Vec d) ((l/2)/μ),
        ρ x = s4PhysicalRho hd ω μ x ∧ α x = s4PhysicalAlpha hd ω μ x) ∧
      IsSpectralDirichletFundamentalSolution ρ α ((l/2)/μ) K G

/-- Native short-time half-mass input on each physical scaled ball. -/
@[nolint defsWithUnderscore]
def b_native_half_mass_input (d : ℕ) (hd : 2 ≤ d) (l κ δ : ℝ) : Prop :=
  ∀ (ω : FieldPair d) (μ : ℝ), 0 < μ → μ ≤ 1 →
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d)
      (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
    IsUniformlyElliptic κ ρ α →
    (∀ x ∈ sourceBall (0 : Vec d) ((l/2)/μ),
      ρ x = s4PhysicalRho hd ω μ x ∧ α x = s4PhysicalAlpha hd ω μ x) →
    IsSpectralDirichletFundamentalSolution ρ α ((l/2)/μ) K G →
    ∀ (x : Vec d) (r u : ℝ), 0 < r →
      sourceBall x (2*r) ⊆ sourceBall 0 ((l/2)/μ) → 0 < u → u ≤ δ*r^2 →
      (1/2 : ℝ) ≤ ∫ y in sourceBall 0 ((l/2)/μ), K u x y

/-- Native short-time comparison input, in source-normalized form. -/
@[nolint defsWithUnderscore]
def b_native_local_comparison_input (d : ℕ) (hd : 2 ≤ d) (l κ δ H : ℝ) : Prop :=
  ∀ (ω : FieldPair d) (μ : ℝ), 0 < μ → μ ≤ 1 →
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d)
      (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
    IsUniformlyElliptic κ ρ α →
    (∀ x ∈ sourceBall (0 : Vec d) ((l/2)/μ),
      ρ x = s4PhysicalRho hd ω μ x ∧ α x = s4PhysicalAlpha hd ω μ x) →
    IsSpectralDirichletFundamentalSolution ρ α ((l/2)/μ) K G →
    ∀ (x y : Vec d) (r u : ℝ), 0 < r →
      sourceBall x (2*r) ⊆ sourceBall 0 ((l/2)/μ) →
      y ∈ sourceBall 0 ((l/2)/μ) → 0 < u → u ≤ δ*r^2 →
      euclideanSq (x-y) ≤ u → K (2*u) x x / ρ x ≤ H * (K (4*u) x y / ρ y)

/-- The three explicit analytic inputs imply the exact local-return ABI. -/
theorem b_centered_local_return_input_of_native_inputs
    (hinputs : ∀ (d : ℕ) (hd : 2 ≤ d) (L l : ℝ), 0 < l →
      ∃ κ δ H : ℝ, 0 < κ ∧ 0 < δ ∧ 0 < H ∧
        b_native_spectral_input d hd L l κ ∧ b_native_half_mass_input d hd l κ δ ∧
        b_native_local_comparison_input d hd l κ δ H) :
    b_centered_local_return_input := by
  intro d hd L r₀ l hl
  obtain ⟨κ, δ, H, hκ, hδ, hH, hkernel, hmass, hcompare⟩ := hinputs d hd L l hl
  obtain ⟨ε, hε, hbound⟩ := b_scaled_centered_return_of_native_short_time
    d hd κ δ H (l/2) 1 hκ hδ hH (by positivity) (by norm_num)
  refine ⟨1, min ε 1, by norm_num, lt_min hε (by norm_num), min_le_right _ _, ?_⟩
  intro Q lam h0 h1 P hP
  filter_upwards [hP] with ω hωP
  obtain ⟨hω, R, hrow⟩ := hωP
  intro c y hy
  let η := zeroPotentialReducedPair ω
  let hωc : IsRegular (sourceReducedBound L) (translate c η) :=
    (ActualImageLpStateTransport.isRegular_translate_iff c η).mpr hω
  let R' := Classical.choice (u5_regular_signed_fixed_environment_realization_exists
    hd (one_le_sourceReducedBound Q.ellipticity_parameter) (translate c η) hωc |lam| h0.le h1)
  obtain ⟨ρ, α, K, G, hell, hcoeff, hK⟩ := hkernel (translate c η) hωc |lam| h0 h1
  have hy' : y-c ∈ sourceBall (0 : Vec d) (((l/2)/|lam|)/2) := by
    change euclideanNorm (y-c-0) < ((l/2)/|lam|)/2
    simp only [sub_zero]
    convert hy using 1 <;> ring
  have hb := hbound |lam| h0 h1 R' ρ α hell hcoeff K G hK
    (hmass (translate c η) |lam| h0 h1 ρ α K G hell hcoeff hK)
    (hcompare (translate c η) |lam| h0 h1 ρ α K G hell hcoeff hK) (y-c) hy'
  have ht := b_centered_return_of_translated_environment hd (sourceReducedBound L)
    (one_le_sourceReducedBound Q.ellipticity_parameter) η hω |lam| h0.le h1 c hωc R R'
    y (1/|lam|^2).toNNReal ((l/2)/|lam|)
  rw [ht] at hb
  rw [hrow y]
  apply (ENNReal.ofReal_le_ofReal (min_le_left ε 1)).trans
  have heq : (l/2)/|lam| = (l/|lam|)/2 := by ring
  have heq2 : (l/|lam|)/2/2 = (l/|lam|)/4 := by ring
  simpa [heq, heq2] using hb

/-- The established local-return consumer gives the full renewal-time tube. -/
theorem b_all_radius_centered_tube_of_native_inputs
    (hinputs : ∀ (d : ℕ) (hd : 2 ≤ d) (L l : ℝ), 0 < l →
      ∃ κ δ H : ℝ, 0 < κ ∧ 0 < δ ∧ 0 < H ∧
        b_native_spectral_input d hd L l κ ∧ b_native_half_mass_input d hd l κ δ ∧
        b_native_local_comparison_input d hd l κ δ H) :
    ∀ {d : ℕ} (hd : 2 ≤ d) (L r₀ l : ℝ), 0 < l →
      ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
        ∀ (Q : EnvironmentLaw d L r₀) (lam : ℝ)
          (h0 : 0 < |lam|) (h1 : |lam| ≤ 1),
          ∃ P : QuenchedPathLaws d,
            IsGMPReducedKernel hd Q.ellipticity_parameter Q |lam| h0.le h1 P ∧
            ∀ᵐ ω ∂Q.measure, ∀ x : Vec d,
              ENNReal.ofReal ε ≤ P (x, ω)
                {γ : Path d | ∀ s ∈ Set.Icc (0 : ℝ≥0)
                    (Regeneration.Renewal.regenDelta |lam|),
                  euclideanNorm (γ s - x) ≤ (l / |lam|) / 2} :=
  b_centered_tube_of_local_return (b_centered_local_return_input_of_native_inputs hinputs)

#print axioms b_centered_local_return_input_of_native_inputs
#print axioms b_all_radius_centered_tube_of_native_inputs
#print axioms b_centered_return_of_translated_environment
#print axioms b_scaled_centered_return_of_native_short_time
#print axioms b_centered_return_of_native_lower
end EinsteinFull
