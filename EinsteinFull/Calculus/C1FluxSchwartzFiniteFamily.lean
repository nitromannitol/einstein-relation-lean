import EinsteinFull.Calculus.C6IndependentBlocksAssembly
import EinsteinFull.Calculus.C1FluxGeneralTestAssembly
import EinsteinFull.Calculus.C1FluxSchwartzSiteAssembly
import EinsteinFull.Calculus.C1FluxSchwartzScaling
import EinsteinFull.Calculus.C19FluxActualSingleBlockBounds
import EinsteinFull.Calculus.CarverSFluxGaussianGain
import EinsteinFull.Blueprint.G2.node_l_u3A_forced_u2D_flux_u23_parameters
import EinsteinFull.Blueprint.G2.node_e_u3A_flux_u2D_block

noncomputable section
open MeasureTheory EinsteinRelation
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint

/-- Reconstruct a finite family of already centered blocks from its local
conditional expectations and annular residual bounds. -/
theorem c1_centered_family_annular_reconstruction {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) {p r R F L τ : ℝ}
    (hp : 2 ≤ p) (hr : 1 ≤ r) (hR : 0 ≤ R)
    (hF : 0 ≤ F) (hL : 0 ≤ L) (hτ : 0 < τ)
    (X : (Fin d → ℤ) → FieldPair d → ℂ) (w : (Fin d → ℤ) → ℝ)
    (hw : ∀ z, 0 ≤ w z)
    (hX : ∀ z, MemLp (X z) (ENNReal.ofReal p) (reducedLaw Q))
    (hX0 : ∀ z, ∫ ω, X z ω ∂(reducedLaw Q) = 0)
    (hbound : ∀ z, (eLpNorm (X z) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ F * w z) :
    let center := fun (z : Fin d → ℤ) (j : Fin d) => r * (z j : ℝ)
    let CE := fun (n : ℕ) z => (reducedLaw Q)[X z | localSigma
      {y : Vec d | euclideanNorm (y - center z) < R * 2 ^ (n + 1) * r}]
    (∀ n z, (eLpNorm (X z - CE n z) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
      L * Real.exp (-4 ^ n * τ) * w z) →
    ∀ S : Finset (Fin d → ℤ),
      MemLp (∑ z ∈ S, X z) (ENNReal.ofReal p) (reducedLaw Q) ∧
      (eLpNorm (∑ z ∈ S, X z) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        EinsteinFull.Calculus.K3.blockColorConst d p r₀ R *
        (F + 2 * L * ∑' n : ℕ, (2 : ℝ) ^ ((n : ℝ) * (d : ℝ) / 2) *
          Real.exp (-4 ^ n * τ)) * Real.sqrt (∑ z ∈ S, w z ^ 2) := by
  intro center CE hloc S
  let _ := reducedLaw_probability Q
  have hp1 : 1 ≤ p := le_trans (by norm_num) hp
  have hq : (1 : ENNReal) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr hp1
  have hCE : ∀ n z, MemLp (CE n z) (ENNReal.ofReal p) (reducedLaw Q) :=
    fun n z => (hX z).condExp hq
  have hcon : ∀ z, (eLpNorm (CE 0 z) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
      (eLpNorm (X z) (ENNReal.ofReal p) (reducedLaw Q)).toReal := fun z =>
    ENNReal.toReal_mono (hX z).eLpNorm_ne_top (eLpNorm_condExp_le_eLpNorm _ hq)
  obtain ⟨hbase, hann⟩ := EinsteinFull.Calculus.K3.block_condExp_square_sums
    Q hp hr hR X hX hX0
  have hcolor : 0 ≤ EinsteinFull.Calculus.K3.blockColorConst d p r₀ R := by
    unfold EinsteinFull.Calculus.K3.blockColorConst EinsteinFull.Calculus.K1.lpSqConst
      Homogenization.IndependentSums.rosenthalBennettIntegralConst
    have hp0 : 0 ≤ p := le_trans (by norm_num) hp
    have hr₀ : 0 ≤ r₀ := by linarith [Q.range_parameter]
    positivity
  exact EinsteinFull.Calculus.K5.fixed_data_annular_reconstruction hp1 d X CE w F L τ _
    hF hL hτ hcolor hw hX hCE hcon hbound hloc hbase hann S

/-- Time-by-time assembly of the cutoff-Schwartz finite family from the
single-block site oracle. -/
theorem c1_schwartz_time_assembly (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (κ η η₀ Cloc Cm t₀ growth₀ : ℝ) (Lmax : ℕ) (hκ : 0 < κ) (hκhalf : κ < 1 / 2)
    (hη : η = κ / (16 * ((d : ℝ) + 2))) (hη₀ : η₀ = η / 4) (hCloc : 1 ≤ Cloc)
    (hCm : 0 < Cm) (ht₀ : 1 ≤ t₀) (hg : 0 < growth₀) (p : ℝ) (hp : 2 ≤ p)
    (ctest : ℝ) (hctest : 0 < ctest) (Btest : ℕ → ℝ) (hBtest : ∀ q, 0 < Btest q) :
    ∃ ttest Cfin : ℝ, t₀ ≤ ttest ∧ 0 < Cfin ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
        (J : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q)) (ζ : ℂ) (t : ℝ≥0),
      ttest ≤ (t : ℝ) → ‖ζ‖ * Real.sqrt (t : ℝ) ≤ (t : ℝ) ^ η₀ →
      ∀ growth K : ℝ, growth₀ ≤ growth → 1 ≤ K → ∀ s : ℝ, 1 ≤ s →
      ∀ (k : ℕ) (ψ : SchwartzMap (Vec d) ℂ), HasGaussianTestControl s k ctest Btest ψ →
      ∀ (r : ℝ) (hr0 : 0 < r), r = (t : ℝ) ^ (1 / 2 + η) →
      ∀ (j : Fin d) (Λ : Finset (Fin d → ℤ)),
      (∀ (z : Fin d → ℤ) (n : ℕ), FluxSiteOracle Q (J t j) (ENNReal.ofReal p) r hr0
        (fun l => r * (z l : ℝ)) ⟨0, by omega⟩ ⟨0, by omega⟩
        (localSigma {y : Vec d | euclideanNorm (y - fun l => r * (z l : ℝ)) <
          (2 * Real.sqrt (d : ℝ) + 2) * 2 ^ (n + 1) * r})
        (c1OracleQm d κ η Cm Cloc growth K ‖ζ‖ (t : ℝ) r Lmax)
        (c1OracleN d Cm Cloc ‖ζ‖ (t : ℝ) r *
          Real.exp (-4 ^ n * ((t : ℝ) ^ (2 * η) / Cloc)))) →
      MemLp (∑ z ∈ Λ, (centeredComplexLp Q (∫ y : Vec d,
        ((fluxPartitionCutoff r (y - fun i => r * (z i : ℝ)) : ℂ) * ψ (-y)) •
          complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y (J t j)) :
            FieldPair d → ℂ)) (ENNReal.ofReal p) (reducedLaw Q) ∧
      (eLpNorm (∑ z ∈ Λ, (centeredComplexLp Q (∫ y : Vec d,
        ((fluxPartitionCutoff r (y - fun i => r * (z i : ℝ)) : ℂ) * ψ (-y)) •
          complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y (J t j)) :
            FieldPair d → ℂ)) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        Cfin * K * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 2) * (t : ℝ) ^ (-1 - κ / 8) *
          s ^ (-(d : ℝ) / 4 - (k : ℝ) / 2) * (1 + (t : ℝ) / s) ^ ⌈(d : ℝ) / 4 + 1 / 2⌉₊ := by
  have hηpos : 0 < η := by rw [hη]; positivity
  obtain ⟨Cb, hCb, hsite⟩ := c1_schwartz_site_assembly d hd D ctest hctest Btest hBtest
  obtain ⟨Tan, hTan1, hTan⟩ := c1_annular_absorbed_form d hηpos (by linarith : κ < 1) hCloc
  obtain ⟨Clat', hClat', hlat'⟩ := c1_test_lattice_square_sum d hd κ ctest hκ hctest
  let Rr : ℝ := 2 * Real.sqrt (d : ℝ) + 2
  let Ccol : ℝ := EinsteinFull.Calculus.K3.blockColorConst d p D.dependenceRange Rr + 1
  let A : ℝ := ∑' n : ℕ, (2 : ℝ) ^ ((n : ℝ) * (d : ℝ) / 2) *
    Real.exp (-4 ^ n * ((1 / Cloc) / 2))
  have hcolnn : 0 ≤ EinsteinFull.Calculus.K3.blockColorConst d p D.dependenceRange Rr := by
    unfold EinsteinFull.Calculus.K3.blockColorConst EinsteinFull.Calculus.K1.lpSqConst
      Homogenization.IndependentSums.rosenthalBennettIntegralConst
    have hp0 : 0 ≤ p := le_trans (by norm_num) hp
    have hr₀ : 0 ≤ D.dependenceRange := by linarith [D.one_le_dependenceRange]
    positivity
  have hcol : 0 < Ccol := by linarith
  have hA : 0 ≤ A := tsum_nonneg fun _ => by positivity
  let Cfin : ℝ := Ccol * Cb * (1 + 3 * A) * Cm * 2 ^ Lmax * Clat' * (2 * Clat')
  have hCfin : 0 < Cfin := by positivity
  refine ⟨max t₀ Tan, Cfin, le_max_left _ _, hCfin, ?_⟩
  intro Q J ζ t htt hζ growth K hgrowth hK s hs k ψ hψ r hr0 hrdef j Λ horacle
  have ht₀t : t₀ ≤ (t : ℝ) := (le_max_left _ _).trans htt
  have hTt : Tan ≤ (t : ℝ) := (le_max_right _ _).trans htt
  have ht1 : 1 ≤ (t : ℝ) := ht₀.trans ht₀t
  have ht0 : 0 < (t : ℝ) := lt_of_lt_of_le zero_lt_one ht1
  have hr1 : 1 ≤ r := by rw [hrdef]; exact Real.one_le_rpow ht1 (by positivity)
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hq : (1 : ENNReal) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.mpr (by linarith)
  have hgpos : 0 ≤ growth := le_trans hg.le hgrowth
  have hCloc0 : 0 < Cloc := lt_of_lt_of_le zero_lt_one hCloc
  let τ : ℝ := (t : ℝ) ^ (2 * η) / Cloc
  have hτ : 0 < τ := by positivity
  have hRr : 0 ≤ Rr := by positivity
  have hℓ : 0 ≤ 1 + r / Real.sqrt s := by positivity
  let w : (Fin d → ℤ) → ℝ := fun z => s ^ (-(k : ℝ) / 2) *
    sSup ((fun y : Vec d => s ^ (-(d : ℝ) / 2) *
      Real.exp (-ctest * euclideanNorm y ^ 2 / s)) ''
        {y : Vec d | euclideanNorm (y - fun l => r * (z l : ℝ)) ≤ Rr * r})
  let X : (Fin d → ℤ) → FieldPair d → ℂ := fun z =>
    (centeredComplexLp Q (∫ y : Vec d,
      ((fluxPartitionCutoff r (y - fun i => r * (z i : ℝ)) : ℂ) * ψ (-y)) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y (J t j)) :
          FieldPair d → ℂ)
  have hNnn : 0 ≤ c1OracleN d Cm Cloc ‖ζ‖ (t : ℝ) r := by
    unfold c1OracleN; positivity
  have hKbnn : 0 ≤ c1OracleKb d κ growth K ‖ζ‖ (t : ℝ) r := by
    have := hK; unfold c1OracleKb; positivity
  have hQm : 0 ≤ c1OracleQm d κ η Cm Cloc growth K ‖ζ‖ (t : ℝ) r Lmax := by
    have := hNnn; have := hKbnn; unfold c1OracleQm; positivity
  have hsiteApp : ∀ (z : Fin d → ℤ) (n : ℕ),
      MemLp (X z) (ENNReal.ofReal p) (reducedLaw Q) ∧
      (eLpNorm (X z) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        Cb * (1 + r / Real.sqrt s) * c1OracleQm d κ η Cm Cloc growth K ‖ζ‖ (t : ℝ) r Lmax *
          w z ∧
      MemLp (X z - (reducedLaw Q)[X z | localSigma {y : Vec d |
        euclideanNorm (y - fun l => r * (z l : ℝ)) < Rr * 2 ^ (n + 1) * r}])
        (ENNReal.ofReal p) (reducedLaw Q) ∧
      (eLpNorm (X z - (reducedLaw Q)[X z | localSigma {y : Vec d |
        euclideanNorm (y - fun l => r * (z l : ℝ)) < Rr * 2 ^ (n + 1) * r}])
        (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
        Cb * (1 + r / Real.sqrt s) * (c1OracleN d Cm Cloc ‖ζ‖ (t : ℝ) r *
          Real.exp (-4 ^ n * τ)) * w z :=
    fun z n => hsite Q (J t j) (ENNReal.ofReal p) hq s r hs0 hr0 k ψ hψ
      (fun l => r * (z l : ℝ)) ⟨0, by omega⟩ ⟨0, by omega⟩
      (localSigma {y : Vec d | euclideanNorm (y - fun l => r * (z l : ℝ)) <
        Rr * 2 ^ (n + 1) * r}) _ _ hQm (mul_nonneg hNnn (Real.exp_nonneg _)) (horacle z n)
  have hw : ∀ z, 0 ≤ w z := fun z => mul_nonneg (Real.rpow_nonneg hs0.le _)
    ((c1_gaussian_ball_sup s ctest (Rr * r) hs0 hctest (by positivity) _).1)
  have hrec := c1_centered_family_annular_reconstruction Q (p := p) (r := r) (R := Rr)
    (F := Cb * (1 + r / Real.sqrt s) * c1OracleQm d κ η Cm Cloc growth K ‖ζ‖ (t : ℝ) r Lmax)
    (L := Cb * (1 + r / Real.sqrt s) * c1OracleN d Cm Cloc ‖ζ‖ (t : ℝ) r) (τ := τ)
    hp hr1 hRr (by positivity) (by have := hNnn; positivity) hτ X w hw
    (fun z => (hsiteApp z 0).1) (fun z => integral_centeredComplexLp Q _)
    (fun z => (hsiteApp z 0).2.1)
  dsimp only at hrec
  have hrecΛ := hrec (fun n z => by
    have h := (hsiteApp z n).2.2.2
    calc _ ≤ _ := h
      _ = _ := by ring) Λ
  refine ⟨hrecΛ.1, hrecΛ.2.trans ?_⟩
  have hζ' : ‖ζ‖ * Real.sqrt (t : ℝ) ≤ (t : ℝ) ^ (η / 4) := by rw [← hη₀]; exact hζ
  have hann := hTan (t : ℝ) hTt ζ hζ' Lmax K growth Cm hK hgpos hCm.le
  rw [← hrdef] at hann
  have hseries := EinsteinFull.Calculus.K4.summable_two_rpow_mul_exp_neg_four_pow d hτ
  have hSge : Real.exp (-τ) ≤ ∑' n : ℕ, (2 : ℝ) ^ ((n : ℝ) * (d : ℝ) / 2) *
      Real.exp (-4 ^ n * τ) := by
    have := hseries.le_tsum 0 (fun n _ => by positivity)
    simpa using this
  have hP2 : (1 + (t : ℝ) / r ^ 2) ^ Lmax ≤ 2 ^ Lmax := by
    have h2 := c1_recovery_scale_ratio_le_two η (t : ℝ) hηpos.le ht1
    rw [← hrdef] at h2
    exact pow_le_pow_left₀ (by positivity) h2 _
  have hl' := hlat' (t : ℝ) s ht1 hs
  dsimp only at hl'
  rw [← hη, ← hrdef] at hl'
  obtain ⟨hsumE, hsqE, hinfl⟩ := hl'
  have hpb := c1_schwartz_power_budget d κ (t : ℝ) s Clat' hκ ht1 hs hClat'.le
  dsimp only at hpb
  rw [← hη, ← hrdef] at hpb
  have hpb' := hpb hinfl
  have hsw : Real.sqrt (∑ z ∈ Λ, w z ^ 2) ≤ s ^ (-(k : ℝ) / 2) *
      (Clat' * r ^ (-(d : ℝ) / 2) * s ^ (-(d : ℝ) / 4) *
        (1 + r / Real.sqrt s) ^ ((d : ℝ) / 2)) :=
    (c1_finite_sqrt_weight _ (Real.rpow_nonneg hs0.le _) _ w (fun z => rfl) hsumE Λ).trans
      (mul_le_mul_of_nonneg_left hsqE (Real.rpow_nonneg hs0.le _))
  have hbrk := c1_schwartz_series_scalar Cb (1 + r / Real.sqrt s) Cm
    (c1OracleKb d κ growth K ‖ζ‖ (t : ℝ) r) ((1 + (t : ℝ) / r ^ 2) ^ Lmax) (2 ^ Lmax) A
    (c1OracleN d Cm Cloc ‖ζ‖ (t : ℝ) r)
    (∑' n : ℕ, (2 : ℝ) ^ ((n : ℝ) * (d : ℝ) / 2) * Real.exp (-4 ^ n * τ))
    (Real.exp (-τ)) (c1OracleQm d κ η Cm Cloc growth K ‖ζ‖ (t : ℝ) r Lmax) hCb.le hℓ hCm.le
    hKbnn hP2 hA hNnn rfl hSge hann
  have hSnn : 0 ≤ ∑' n : ℕ, (2 : ℝ) ^ ((n : ℝ) * (d : ℝ) / 2) * Real.exp (-4 ^ n * τ) :=
    tsum_nonneg fun _ => by positivity
  have hsp : s ^ (-(d : ℝ) / 4 - (k : ℝ) / 2) = s ^ (-(k : ℝ) / 2) * s ^ (-(d : ℝ) / 4) := by
    rw [← Real.rpow_add hs0]; congr 1; ring
  have hfinal := c1_schwartz_final_chain
    (EinsteinFull.Calculus.K3.blockColorConst d p D.dependenceRange Rr) Ccol Cb
    (1 + r / Real.sqrt s) A Cm (2 ^ Lmax) K (Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 2))
    ((t : ℝ) ^ (-1 - (1 / 2 + (d : ℝ) / 4))) (r ^ ((d : ℝ) + 1 - κ)) (r ^ (-(d : ℝ) / 2))
    ((1 + r / Real.sqrt s) ^ ((d : ℝ) / 2)) (s ^ (-(k : ℝ) / 2)) (s ^ (-(d : ℝ) / 4)) Clat'
    ((1 + (t : ℝ) / s) ^ ⌈(d : ℝ) / 4 + 1 / 2⌉₊) ((t : ℝ) ^ (-1 - κ / 8)) _ _
    (by linarith) hcolnn hCb.le hℓ hA hCm.le (by positivity) (by linarith) (by positivity)
    (by positivity) (by positivity) (by positivity) (by positivity)
    hClat'.le hbrk (by have := hNnn; have := hQm; positivity) hsw
    (Real.sqrt_nonneg _) hpb'
  refine hfinal.trans (le_of_eq ?_)
  rw [hsp]

/-- The finite-family cutoff-Schwartz gain of the forced flux. -/
theorem c1_flux_schwartz_finite_block_gain : node_l_u3A_forced_u2D_flux_u23_independent_u2D_blocksStmtV2 → node_l_u3A_forced_u2D_flux_u23_parametersStmt → node_e_u3A_flux_u2D_blockStmt → ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d), ∃ κ η η₀ ε Clat : ℝ, ∃ L : ℕ → ℕ, 0 < κ ∧ κ < 1 / 2 ∧ η = κ / (16 * ((d : ℝ) + 2)) ∧ η₀ = η / 4 ∧ ε = κ / 8 ∧ 0 < ε ∧ 0 < η₀ ∧ 0 < Clat ∧ -1 - κ / 2 + η * ((d : ℝ) + 1 - κ) ≤ -1 - κ / 4 ∧ (∀ t s : ℝ, 1 ≤ t → 1 ≤ s → ∀ x : Vec d, let r := t ^ (1 / 2 + η); let R := 2 * Real.sqrt (d : ℝ) + 2; let W := fun z : Fin d → ℤ => sSup ((fun y : Vec d => s ^ (-(d : ℝ) / 2) * Real.exp (-euclideanNorm (x - y) ^ 2 / s)) '' {y : Vec d | euclideanNorm (y - fun j => r * (z j : ℝ)) ≤ R * r}); Summable (fun z : Fin d → ℤ => (W z) ^ 2) ∧ Real.sqrt (∑' z : Fin d → ℤ, (W z) ^ 2) ≤ Clat * r ^ (-(d : ℝ) / 2) * s ^ (-(d : ℝ) / 4) * (1 + r / Real.sqrt s) ^ ((d : ℝ) / 2) ∧ (1 + r / Real.sqrt s) ^ ((d : ℝ) / 2) ≤ Clat * t ^ (η * (d : ℝ) / 2) * (1 + t / s) ^ ((d : ℝ) / 4)) ∧ ∀ p : ℝ, 2 ≤ p → ∃ growth₀ t₀ : ℝ, ∃ Cder : ℕ → ℝ, 0 < growth₀ ∧ 1 ≤ t₀ ∧ (∀ k, 0 < Cder k) ∧ ∀ ctest : ℝ, 0 < ctest → ∀ Btest : ℕ → ℝ, (∀ q, 0 < Btest q) → ∃ ttest : ℝ, ∃ Ctest : ℕ → ℝ, t₀ ≤ ttest ∧ (∀ k, 0 < Ctest k) ∧ ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)), IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ → ∀ ζ : ℂ, ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q), IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P → IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d, ∃ G J : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q), (∀ t : ℝ≥0, 0 < (t : ℝ) → IsEndpointWeakFlux hd Q ν ζ a (indexedEndpoint hd Q ν ζ P Pdag β a μ t) (G t) (J t)) ∧ ∀ (t : ℝ≥0), ttest ≤ (t : ℝ) → ‖ζ‖ * Real.sqrt (t : ℝ) ≤ (t : ℝ) ^ η₀ → ∀ growth K : ℝ, growth₀ ≤ growth → 1 ≤ K → MemLp (indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8) : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) → (eLpNorm (indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8) : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ K * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 8) * (((t : ℝ) / 8) ^ (-(1 / 2 + (d : ℝ) / 4)) + ‖ζ‖ * ((t : ℝ) / 8) ^ (-(d : ℝ) / 4)) → ∀ (s : ℝ), 1 ≤ s → ∀ (k : ℕ) (ψ : SchwartzMap (Vec d) ℂ), HasGaussianTestControl s k ctest Btest ψ → let r := (t : ℝ) ^ (1/2 + η); ∀ (j : Fin d) (Λ : Finset (Fin d → ℤ)), let b := fun z : Fin d → ℤ => centeredComplexLp Q (∫ y : Vec d, ((fluxPartitionCutoff r (y - fun i => r * (z i : ℝ)) : ℂ) * ψ (-y)) • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y (J t j)); MemLp (∑ z ∈ Λ, (b z : FieldPair d → ℂ)) (ENNReal.ofReal p) (reducedLaw Q) ∧ (eLpNorm (∑ z ∈ Λ, (b z : FieldPair d → ℂ)) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ Ctest k * K * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 2) * (t : ℝ) ^ (-1 - ε) * s ^ (-(d : ℝ) / 4 - (k : ℝ) / 2) * (1 + (t : ℝ) / s) ^ L k := by
  intro hV2 _hpar _hblock d hd D
  obtain ⟨κ, η, η₀, Cenv, Lblock, hκ, hκhalf, hCenv, hη, hη₀, hv⟩ :=
    c19_v2_actual_single_block_bounds hV2 d hd D
  obtain ⟨Clat, hClat, hlat⟩ :=
    carverS_flux_lattice_square_sum_fixed_parameters d hd κ 1 hκ le_rfl
  have hηpos : 0 < η := by rw [hη]; positivity
  refine ⟨κ, η, η₀, κ / 8, Clat, fun _ => ⌈(d : ℝ) / 4 + 1 / 2⌉₊, hκ, hκhalf, hη, hη₀, rfl,
    by positivity, by rw [hη₀]; positivity, hClat, ?_, ?_, ?_⟩
  · simpa only [← hη] using flux_lattice_exponent_margin d κ hκ
  · intro t s ht hs x
    simpa only [one_mul, ← hη] using hlat t s ht hs x
  · intro p hp
    obtain ⟨growth₀, t₀, Cloc, Cder, hg, ht₀, hCloc, hCder, hv⟩ := hv p hp
    refine ⟨growth₀, t₀, Cder, hg, ht₀, fun k => lt_of_lt_of_le zero_lt_one (hCder k), ?_⟩
    intro ctest hctest Btest hBtest
    have hCd0 : 0 ≤ Cder 0 := le_trans zero_le_one (hCder 0)
    have hCd1 : 0 ≤ Cder 1 := le_trans zero_le_one (hCder 1)
    have hCm : 0 < Cder 0 + Cder 1 := by linarith [hCder 0, hCder 1]
    obtain ⟨ttest, Cfin, httest, hCfin, hB⟩ := c1_schwartz_time_assembly d hd D κ η η₀ Cloc
      (Cder 0 + Cder 1) t₀ growth₀ (Lblock 0 + Lblock 1) hκ hκhalf hη hη₀ hCloc hCm ht₀ hg
      p hp ctest hctest Btest hBtest
    refine ⟨ttest, fun _ => Cfin, httest, fun _ => hCfin, ?_⟩
    intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
    obtain ⟨G, J, hflux, hfin⟩ := hv Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
    refine ⟨G, J, hflux, ?_⟩
    intro t htt hζ growth K hgrowth hK hmem hbound s hs k ψ hψ
    dsimp only
    have ht₀t : t₀ ≤ (t : ℝ) := httest.trans htt
    have ht1 : 1 ≤ (t : ℝ) := ht₀.trans ht₀t
    have ht0 : 0 < (t : ℝ) := lt_of_lt_of_le zero_lt_one ht1
    obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = (t : ℝ) ^ (1 / 2 + η) := ⟨_, rfl⟩
    rw [← hrdef]
    intro j Λ
    have hr0 : 0 < r := by rw [hrdef]; exact Real.rpow_pos_of_pos ht0 _
    have hr1 : 1 ≤ r := by rw [hrdef]; exact Real.one_le_rpow ht1 (by positivity)
    have hr2 : 1 ≤ r ^ 2 := one_le_pow₀ hr1
    have hCloc0 : 0 < Cloc := lt_of_lt_of_le zero_lt_one hCloc
    have hl : 1 ≤ 1 + (t : ℝ) / r ^ 2 := by
      have : 0 ≤ (t : ℝ) / r ^ 2 := by positivity
      linarith
    have hKb : 0 ≤ c1OracleKb d κ growth K ‖ζ‖ (t : ℝ) r := by
      have := hK
      unfold c1OracleKb
      positivity
    have hfin' := hfin t ht₀t hζ growth K hgrowth hK hmem hbound (r ^ 2) hr2 (sq_pos_of_pos hr0)
    have hexp0 : Real.exp (Cloc * ‖ζ‖ ^ 2 * (t : ℝ) - (t : ℝ) ^ (2 * η) / Cloc) =
        Real.exp (Cloc * ‖ζ‖ ^ 2 * (t : ℝ)) * Real.exp (-((t : ℝ) ^ (2 * η) / Cloc)) := by
      rw [← Real.exp_add]; congr 1
    have hexpn (n : ℕ) : Real.exp (Cloc * ‖ζ‖ ^ 2 * (t : ℝ) - 4 ^ n * (t : ℝ) ^ (2 * η) / Cloc) =
        Real.exp (Cloc * ‖ζ‖ ^ 2 * (t : ℝ)) *
          Real.exp (-4 ^ n * ((t : ℝ) ^ (2 * η) / Cloc)) := by
      rw [← Real.exp_add]; congr 1; ring
    let i0 : Fin d := ⟨0, by omega⟩
    have horacle : ∀ (z : Fin d → ℤ) (n : ℕ), FluxSiteOracle Q (J t j) (ENNReal.ofReal p) r hr0
        (fun l => r * (z l : ℝ)) ⟨0, by omega⟩ ⟨0, by omega⟩
        (localSigma {y : Vec d | euclideanNorm (y - fun l => r * (z l : ℝ)) <
          (2 * Real.sqrt (d : ℝ) + 2) * 2 ^ (n + 1) * r})
        (c1OracleQm d κ η (Cder 0 + Cder 1) Cloc growth K ‖ζ‖ (t : ℝ) r (Lblock 0 + Lblock 1))
        (c1OracleN d (Cder 0 + Cder 1) Cloc ‖ζ‖ (t : ℝ) r *
          Real.exp (-4 ^ n * ((t : ℝ) ^ (2 * η) / Cloc))) := by
      intro z n θ h1 h2 h3 h4 h5 h6 b
      have hpart : ∀ y : Vec d, (∑' z : Fin d → ℤ, θ (y - fun l => r * (z l : ℝ))) = 1 :=
        fun y => (h6 y).tsum_eq
      have hW' : 0 ≤ sSup ((fun y : Vec d => (r ^ 2) ^ (-(d : ℝ) / 2) *
          Real.exp (-euclideanNorm ((fun l => r * (z l : ℝ)) - y) ^ 2 / (Cenv * r ^ 2))) ''
            {y : Vec d | euclideanNorm (y - fun l => r * (z l : ℝ)) ≤
              (2 * Real.sqrt (d : ℝ) + 2) * r}) :=
        Real.sSup_nonneg (by rintro _ ⟨y, _, rfl⟩; positivity)
      obtain ⟨hV0, hV1⟩ := c1_recovery_envelope_prefactors r Cenv
        ((2 * Real.sqrt (d : ℝ) + 2) * r) hr0 (by linarith) (by positivity)
        (fun l => r * (z l : ℝ)) (fun l => r * (z l : ℝ))
      cases b
      · have h := hfin' 1 (fun _ => i0) θ h1 h2 (by rw [← hrdef]; exact h3) h4
          (by rw [← hrdef]; exact h5) (by rw [← hrdef]; exact hpart)
          (fun l => r * (z l : ℝ)) j z
        dsimp only at h
        rw [← hrdef] at h
        simp only [c1_iterated_one_apply, Nat.cast_one] at h
        simp only [Bool.false_eq_true, ↓reduceIte]
        have hVn : 0 ≤ (r ^ 2) ^ (-(1 : ℝ) / 2) * sSup ((fun y : Vec d => (r ^ 2) ^ (-(d : ℝ) / 2) *
          Real.exp (-euclideanNorm ((fun l => r * (z l : ℝ)) - y) ^ 2 / (Cenv * r ^ 2))) ''
            {y : Vec d | euclideanNorm (y - fun l => r * (z l : ℝ)) ≤
              (2 * Real.sqrt (d : ℝ) + 2) * r}) := by positivity
        refine ⟨h.1, ?_, (h.2.2 n).1, ?_⟩
        · refine h.2.1.trans ?_
          refine le_of_eq_of_le ?_ ((c1_oracle_scalar (Cder 1) (Cder 0 + Cder 1)
            ((1 + (t : ℝ) / r ^ 2) ^ Lblock 1) ((1 + (t : ℝ) / r ^ 2) ^ (Lblock 0 + Lblock 1)) (c1OracleKb d κ growth K ‖ζ‖ (t : ℝ) r)
            ((2 + (t : ℝ)) ^ Cloc * Real.exp (Cloc * ‖ζ‖ ^ 2 * (t : ℝ)) * r ^ d *
              Real.exp (-((t : ℝ) ^ (2 * η) / Cloc))) _ (r ^ (-(d : ℝ) - 1)) hCd1 (by linarith)
            (by positivity) (pow_le_pow_right₀ hl (Nat.le_add_left _ _)) hKb
            (by positivity) hVn hV1).trans (le_of_eq ?_))
          · rw [hexp0]
            unfold c1OracleKb
            ring
          · unfold c1OracleQm c1OracleN c1OracleKb
            ring
        · refine (h.2.2 n).2.trans ?_
          refine le_of_eq_of_le ?_ ((c1_oracle_scalar_res (Cder 1) (Cder 0 + Cder 1)
            ((2 + (t : ℝ)) ^ Cloc * Real.exp (Cloc * ‖ζ‖ ^ 2 * (t : ℝ)) * r ^ d *
              Real.exp (-4 ^ n * ((t : ℝ) ^ (2 * η) / Cloc))) _ (r ^ (-(d : ℝ) - 1)) (by linarith)
            (by positivity) hVn hV1 hCd1).trans (le_of_eq ?_))
          · rw [hexpn n]
            ring
          · unfold c1OracleN
            ring
      · have h := hfin' 0 (fun i => i.elim0) θ h1 h2 (by rw [← hrdef]; exact h3) h4
          (by rw [← hrdef]; exact h5) (by rw [← hrdef]; exact hpart)
          (fun l => r * (z l : ℝ)) j z
        dsimp only at h
        rw [← hrdef] at h
        simp only [c1_iterated_zero_apply, Nat.cast_zero, neg_zero, zero_div, Real.rpow_zero] at h
        simp only [↓reduceIte]
        refine ⟨h.1, ?_, (h.2.2 n).1, ?_⟩
        · refine h.2.1.trans ?_
          refine le_of_eq_of_le ?_ ((c1_oracle_scalar (Cder 0) (Cder 0 + Cder 1)
            ((1 + (t : ℝ) / r ^ 2) ^ Lblock 0) ((1 + (t : ℝ) / r ^ 2) ^ (Lblock 0 + Lblock 1)) (c1OracleKb d κ growth K ‖ζ‖ (t : ℝ) r)
            ((2 + (t : ℝ)) ^ Cloc * Real.exp (Cloc * ‖ζ‖ ^ 2 * (t : ℝ)) * r ^ d *
              Real.exp (-((t : ℝ) ^ (2 * η) / Cloc))) _ (r ^ (-(d : ℝ))) hCd0 (by linarith)
            (by positivity) (pow_le_pow_right₀ hl (Nat.le_add_right _ _)) hKb
            (by positivity) hW' hV0).trans (le_of_eq ?_))
          · rw [hexp0]
            unfold c1OracleKb
            ring
          · unfold c1OracleQm c1OracleN c1OracleKb
            ring
        · refine (h.2.2 n).2.trans ?_
          refine le_of_eq_of_le ?_ ((c1_oracle_scalar_res (Cder 0) (Cder 0 + Cder 1)
            ((2 + (t : ℝ)) ^ Cloc * Real.exp (Cloc * ‖ζ‖ ^ 2 * (t : ℝ)) * r ^ d *
              Real.exp (-4 ^ n * ((t : ℝ) ^ (2 * η) / Cloc))) _ (r ^ (-(d : ℝ))) (by linarith)
            (by positivity) hW' hV0 hCd0).trans (le_of_eq ?_))
          · rw [hexpn n]
            ring
          · unfold c1OracleN
            ring
    exact hB Q J ζ t htt hζ growth K hgrowth hK s hs k ψ hψ r hr0 hrdef j Λ horacle

end EinsteinFull.Blueprint
