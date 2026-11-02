import EinsteinFull.Calculus.C5TubeSignedMomentLimitAssembly
import EinsteinFull.Calculus.C5TubeSymmetricSignedC2Energy
import EinsteinFull.Calculus.C5TubeAllRealPowerStructure

open EinsteinRelation MeasureTheory EinsteinFull.External.Source.GMP
open PDE hiding Vec Mat
open PDE.Parabolic.LocalMax
open scoped ENNReal NNReal

namespace EinsteinFull.Calculus

/-- The derivative of the symmetric power is controlled by its curvature
and the uncentered symmetric energy. -/
theorem c5_symmetric_truncated_power_derivative_bound {p ε : ℝ}
    (hp : 2 ≤ p) (hε : 0 < ε) (n : ℕ) (s : ℝ) :
    let F := powF p ε (n : ℝ)
    (deriv F s - deriv F (-s)) ^ 2 ≤
      2 * (2 + p / (p - 1)) *
        (deriv (deriv F) s + deriv (deriv F) (-s)) * (F s + F (-s)) := by
  dsimp only
  have h₁ := c5_all_real_truncated_power_structure hp hε n s
  have h₂ := c5_all_real_truncated_power_structure hp hε n (-s)
  dsimp only at h₁ h₂
  obtain ⟨hf₁, hc₁, hb₁⟩ := h₁
  obtain ⟨hf₂, hc₂, hb₂⟩ := h₂
  have hp0 : 0 ≤ p := by linarith
  have hp1 : 0 ≤ p - 1 := by linarith
  have hK : 0 ≤ 2 + p / (p - 1) := by positivity
  have hcross₁ : 0 ≤ (2 + p / (p - 1)) *
      deriv (deriv (powF p ε (n : ℝ))) s * powF p ε (n : ℝ) (-s) := by positivity
  have hcross₂ : 0 ≤ (2 + p / (p - 1)) *
      deriv (deriv (powF p ε (n : ℝ))) (-s) * powF p ε (n : ℝ) s := by positivity
  nlinarith [sq_nonneg (deriv (powF p ε (n : ℝ)) s +
    deriv (powF p ε (n : ℝ)) (-s))]

/-- The structural estimate in the variables of the signed energy identity. -/
theorem c5_symmetric_truncated_energy_derivative_bound {p ε : ℝ}
    (hp : 2 ≤ p) (hε : 0 < ε) (n : ℕ) (s : ℝ) :
    let f := powF p ε (n : ℝ)
    let F := fun x => f x + f (-x) - 2 * f 0
    (deriv F s) ^ 2 ≤ 2 * (2 + p / (p - 1)) *
      deriv (deriv F) s * (f s + f (-s)) := by
  dsimp only
  let f := powF p ε (n : ℝ)
  have hf : ContDiff ℝ 2 f := powF_contDiff hε (Nat.cast_nonneg n)
  have hf' : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hdf : Differentiable ℝ (deriv f) :=
    (PDE.Parabolic.Chain.contDiff_deriv_of_two hf).differentiable (by norm_num)
  have hfirst : deriv (fun x => f x + f (-x) - 2 * f 0) =
      (fun x => deriv f x - deriv f (-x)) := by
    funext x
    change deriv (f + (f ∘ Neg.neg) - (fun _ => 2 * f 0)) x = _
    rw [deriv_sub (hf'.add (hf'.comp differentiable_neg)).differentiableAt
      (differentiableAt_const _), deriv_add hf'.differentiableAt
      (hf'.comp differentiable_neg).differentiableAt]
    change deriv f x + deriv (fun y => f (-y)) x - deriv (fun _ => 2 * f 0) x = _
    rw [deriv_comp_neg, deriv_const]
    ring
  have hsecond : deriv (deriv (fun x => f x + f (-x) - 2 * f 0)) s =
      deriv (deriv f) s + deriv (deriv f) (-s) := by
    rw [hfirst]
    change deriv (deriv f - (deriv f ∘ Neg.neg)) s = _
    rw [deriv_sub hdf.differentiableAt (hdf.comp differentiable_neg).differentiableAt]
    change deriv (deriv f) s - deriv (fun x => deriv f (-x)) s = _
    rw [deriv_comp_neg, sub_neg_eq_add]
  change (deriv (fun x => f x + f (-x) - 2 * f 0) s) ^ 2 ≤ _
  rw [hsecond, hfirst]
  exact c5_symmetric_truncated_power_derivative_bound hp hε n s

/-- Young absorption for the flux term in the symmetric signed energy identity. -/
theorem c5_symmetric_truncated_energy_cross_bound {d : ℕ} {κ p ε : ℝ}
    (hκ : 0 < κ) (hp : 2 ≤ p) (hε : 0 < ε) (n : ℕ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (x e v : Vec d) (s η : ℝ) :
    let f := powF p ε (n : ℝ)
    let F := fun y => f y + f (-y) - 2 * f 0
    |deriv F s * (2 * η * dot ((α x).mulVec e) v)| ≤
      (1 / 2 : ℝ) * deriv (deriv F) s * dot e ((α x).mulVec e) * η ^ 2 +
      2 * κ⁻¹ * (2 * (2 + p / (p - 1))) * (f s + f (-s)) * euclideanSq v := by
  dsimp only
  let f := powF p ε (n : ℝ)
  let F := fun y => f y + f (-y) - 2 * f 0
  have hf : ContDiff ℝ 2 f := powF_contDiff hε (Nat.cast_nonneg n)
  have hf' : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hdf : Differentiable ℝ (deriv f) :=
    (PDE.Parabolic.Chain.contDiff_deriv_of_two hf).differentiable (by norm_num)
  have hfirst : deriv F = (fun y => deriv f y - deriv f (-y)) := by
    funext y
    change deriv (f + (f ∘ Neg.neg) - (fun _ => 2 * f 0)) y = _
    rw [deriv_sub (hf'.add (hf'.comp differentiable_neg)).differentiableAt
      (differentiableAt_const _), deriv_add hf'.differentiableAt
      (hf'.comp differentiable_neg).differentiableAt]
    change deriv f y + deriv (fun z => f (-z)) y - deriv (fun _ => 2 * f 0) y = _
    rw [deriv_comp_neg, deriv_const]
    ring
  have hsecond : deriv (deriv F) s = deriv (deriv f) s + deriv (deriv f) (-s) := by
    rw [hfirst]
    change deriv (deriv f - (deriv f ∘ Neg.neg)) s = _
    rw [deriv_sub hdf.differentiableAt (hdf.comp differentiable_neg).differentiableAt]
    change deriv (deriv f) s - deriv (fun y => deriv f (-y)) s = _
    rw [deriv_comp_neg, sub_neg_eq_add]
  have hs := c5_all_real_truncated_power_structure hp hε n s
  have hneg := c5_all_real_truncated_power_structure hp hε n (-s)
  dsimp only at hs hneg
  have hF0 : 0 ≤ f s + f (-s) := add_nonneg hs.1 hneg.1
  have hF2 : 0 ≤ deriv (deriv F) s := by rw [hsecond]; exact add_nonneg hs.2.1 hneg.2.1
  have hp0 : 0 ≤ p := by linarith
  have hp1 : 0 ≤ p - 1 := by linarith
  have hK : 0 ≤ 2 * (2 + p / (p - 1)) := by positivity
  have hQ : 0 ≤ dot e ((α x).mulVec e) := by
    have he := (hell.2.2 x).2.2.2 e |>.1
    change κ * euclideanSq e ≤ dot e ((α x).mulVec e) at he
    exact (mul_nonneg hκ.le (PDE.vecNormSq_nonneg e)).trans he
  have hy := PDE.Parabolic.LocalMax.abs_young_le
    (F0 := f s + f (-s)) (F1 := deriv F s) (F2 := deriv (deriv F) s)
    (K := 2 * (2 + p / (p - 1))) (L := κ⁻¹)
    (Q := dot e ((α x).mulVec e)) (N := euclideanSq v) (η := η) (χ := 1)
    (P := dot ((α x).mulVec e) v)
    hF0 hF2 hK (inv_nonneg.mpr hκ.le) hQ (PDE.vecNormSq_nonneg v)
    (by norm_num) (c5_symmetric_truncated_energy_derivative_bound hp hε n s)
    (c11_weighted_flux_cross_bound hκ hell x e v)
  simpa only [mul_one] using hy

/-- Both signed Sobolev truncations control the regularized absolute moment
on a set where the cutoff is one. -/
theorem c5_signed_cutoff_powG_moment_bound {d : ℕ}
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} {I : Set ℝ} {U : Set (Vec d)}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hcal : IsWeightedCaloric ρ α I U u G)
    (S : Set (ℝ × Vec d)) (hS : MeasurableSet S) (hSV : S ⊆ I ×ˢ U)
    (η : ℝ × Vec d → ℝ) (hη : ∀ z ∈ S, η z = 1)
    (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε) (B : ℝ≥0∞)
    (hbound : ∀ n : ℕ,
      (∫⁻ z in I ×ˢ U,
        ENNReal.ofReal |η z * powG p ε n (u z)| ^ (2 * ((d : ℝ) + 2) / d) +
        ENNReal.ofReal |η z * powG p ε n (-u z)| ^ (2 * ((d : ℝ) + 2) / d)) ≤ B) :
    (∫⁻ z in S, ENNReal.ofReal (|u z| + ε) ^ (p * (((d : ℝ) + 2) / d))) ≤ B := by
  let q : ℝ := 2 * ((d : ℝ) + 2) / d
  let μ := volume.restrict S
  have hu : AEMeasurable u μ := hcal.1.aemeasurable.mono_measure
    (Measure.restrict_mono_set volume hSV)
  have hmeas : ∀ n : ℕ, AEMeasurable (fun z =>
      ENNReal.ofReal |powG p ε n (u z)| ^ q +
      ENNReal.ofReal |powG p ε n (-u z)| ^ q) μ := by
    intro n
    have hg : Continuous (powG p ε n) := (powG_contDiff hε (Nat.cast_nonneg n)).continuous
    exact ((ENNReal.measurable_ofReal.comp_aemeasurable
      ((hg.measurable.comp_aemeasurable hu).abs)).pow_const q).add
      ((ENNReal.measurable_ofReal.comp_aemeasurable
        ((hg.measurable.comp_aemeasurable hu.neg).abs)).pow_const q)
  have hpoint : ∀ z, ENNReal.ofReal (|u z| + ε) ^ (p * (((d : ℝ) + 2) / d)) ≤
      Filter.liminf (fun n : ℕ => ENNReal.ofReal |powG p ε n (u z)| ^ q +
        ENNReal.ofReal |powG p ε n (-u z)| ^ q) Filter.atTop := by
    intro z
    apply Filter.le_liminf_of_le (by isBoundedDefault)
    obtain ⟨N, hN⟩ := exists_nat_ge |u z|
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    have hn' : |u z| ≤ (n : ℝ) := hN.trans (Nat.cast_le.mpr hn)
    by_cases hz : 0 ≤ u z
    · have hpow := powG_eq_of_le (p := p) (N := (n : ℝ)) hε hz
        (Or.inr (by simpa [abs_of_nonneg hz] using hn'))
      rw [abs_of_nonneg hz, ← PDE.Parabolic.LocalMax.ofReal_half_pow_rpow
        (by linarith : 0 ≤ u z + ε) (by linarith : 0 ≤ p), ← hpow]
      exact le_add_right le_rfl
    · have hz' : 0 ≤ -u z := neg_nonneg.mpr (le_of_not_ge hz)
      have hpow := powG_eq_of_le (p := p) (N := (n : ℝ)) hε hz'
        (Or.inr (by simpa [abs_of_nonpos (le_of_not_ge hz)] using hn'))
      rw [abs_of_nonpos (le_of_not_ge hz), ← PDE.Parabolic.LocalMax.ofReal_half_pow_rpow
        (by linarith : 0 ≤ -u z + ε) (by linarith : 0 ≤ p), ← hpow]
      exact le_add_left le_rfl
  calc
    _ ≤ ∫⁻ z, Filter.liminf (fun n : ℕ =>
        ENNReal.ofReal |powG p ε n (u z)| ^ q +
        ENNReal.ofReal |powG p ε n (-u z)| ^ q) Filter.atTop ∂μ := lintegral_mono hpoint
    _ ≤ Filter.liminf (fun n : ℕ => ∫⁻ z,
        ENNReal.ofReal |powG p ε n (u z)| ^ q +
        ENNReal.ofReal |powG p ε n (-u z)| ^ q ∂μ) Filter.atTop := lintegral_liminf_le' hmeas
    _ ≤ B := by
      apply Filter.liminf_le_of_frequently_le'
      apply Filter.Eventually.frequently
      apply Filter.Eventually.of_forall
      intro n
      calc
        _ = ∫⁻ z in S, ENNReal.ofReal |η z * powG p ε n (u z)| ^ q +
              ENNReal.ofReal |η z * powG p ε n (-u z)| ^ q := by
          apply setLIntegral_congr_fun hS
          intro z hz
          simp only [hη z hz, one_mul]
        _ ≤ ∫⁻ z in I ×ˢ U, ENNReal.ofReal |η z * powG p ε n (u z)| ^ q +
              ENNReal.ofReal |η z * powG p ε n (-u z)| ^ q := lintegral_mono_set hSV
        _ ≤ B := hbound n

/-- The structural constant stays uniform throughout the Moser range. -/
theorem c5_truncated_power_structure_constant_le_four {p : ℝ} (hp : 2 ≤ p) :
    2 + p / (p - 1) ≤ 4 := by
  have hden : 0 < p - 1 := by linarith
  have hquot : p / (p - 1) ≤ 2 := (div_le_iff₀ hden).2 (by linarith)
  linarith

/-- Either signed half-power derivative is controlled by the symmetric
truncated curvature, including on the affine negative branch. -/
theorem c5_signed_powG_derivative_curvature_bound {p ε : ℝ}
    (hp : 2 ≤ p) (hε : 0 < ε) (n : ℕ) (s : ℝ) :
    (deriv (powG p ε n) s) ^ 2 ≤
      (2 + p / (p - 1)) *
        (deriv (deriv (powF p ε n)) s + deriv (deriv (powF p ε n)) (-s)) := by
  have hp1 : 1 < p := by linarith
  have hp0 : 0 ≤ p := by linarith
  have hpm : 0 ≤ p - 1 := by linarith
  have hN : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hK : 0 ≤ 2 + p / (p - 1) := by positivity
  have hmain : (deriv (powG p ε n) s) ^ 2 ≤
      (2 + p / (p - 1)) * deriv (deriv (powF p ε n)) s := by
    by_cases hs : 0 ≤ s
    · exact (c11_truncated_power_energy_structure hp1 hε n s hs).2.2.2.2.1
    · have hs' : s ≤ 0 := le_of_not_ge hs
      have hcap : powCap p ε n s = powCap p ε n 0 := by
        unfold powCap
        rw [max_eq_right (by linarith : s + ε ≤ ε)]
        simp only [zero_add, max_self]
      have hzero := (c11_truncated_power_energy_structure hp1 hε n 0 le_rfl).2.2.2.2.1
      rw [deriv_powG hε hN, deriv_deriv_powF hε hN] at hzero ⊢
      unfold powG1 powF2 at hzero ⊢
      rw [hcap]
      exact hzero
  have hother : 0 ≤ deriv (deriv (powF p ε n)) (-s) := by
    rw [deriv_deriv_powF hε hN]
    exact powF2_nonneg hp1 hε hN _
  have := mul_nonneg hK hother
  nlinarith

/-- On the negative branch the half-power is controlled by the energy itself. -/
theorem c5_powG_sq_le_powF_of_nonpos {p ε : ℝ}
    (hp : 2 ≤ p) (hε : 0 < ε) (n : ℕ) {s : ℝ} (hs : s ≤ 0) :
    powG p ε n s ^ 2 ≤ powF p ε n s := by
  have hN : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hi : ∫ r in (0 : ℝ)..s, powG1 p ε n r =
      ∫ _r in (0 : ℝ)..s, p / 2 * ε ^ (p / 2 - 1) := by
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [Set.uIcc_of_ge hs] at hr
    simp only [powG1, c5_power_cap_of_nonpos hN hr.2]
  have hg : powG p ε n s = ε ^ (p / 2) + p / 2 * ε ^ (p / 2 - 1) * s := by
    unfold powG
    rw [hi, intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    ring
  obtain ⟨hpow1, hpow2, hpow3, hpow4⟩ := rpow_split hε p
  rw [hg, c5_power_energy_of_nonpos hε hN hs, hpow1, hpow2, hpow3]
  have hrem : 0 ≤ ε ^ (p - 2) * p * (p - 2) * s ^ 2 / 4 := by
    positivity
  have heq : (ε ^ (p / 2 - 1) * ε + p / 2 * ε ^ (p / 2 - 1) * s) ^ 2 =
      ε ^ (p - 2) * (ε + p / 2 * s) ^ 2 := by rw [← hpow4]; ring
  rw [heq]
  nlinarith

/-- The truncated half-power is controlled by the truncated energy for all signs. -/
theorem c5_powG_sq_le_powF {p ε : ℝ}
    (hp : 2 ≤ p) (hε : 0 < ε) (n : ℕ) (s : ℝ) :
    powG p ε n s ^ 2 ≤ (2 + p / (p - 1)) * powF p ε n s := by
  by_cases hs : 0 ≤ s
  · exact (c11_truncated_power_energy_structure (by linarith : 1 < p) hε n s hs).2.2.2.1
  · have hf := (c5_all_real_truncated_power_structure hp hε n s).1
    have hp0 : 0 ≤ p := by linarith
    have hp1 : 0 ≤ p - 1 := by linarith
    have hK : 1 ≤ 2 + p / (p - 1) := by
      have : 0 ≤ p / (p - 1) := div_nonneg hp0 hp1
      linarith
    calc
      _ ≤ powF p ε n s := c5_powG_sq_le_powF_of_nonpos hp hε n (le_of_not_ge hs)
      _ ≤ (2 + p / (p - 1)) * powF p ε n s := by nlinarith

/-- Signed weighted slice mass is controlled by the truncated energy. -/
theorem c5_signed_truncated_power_slice_mass_le {d : ℕ}
    {ρ : Vec d → ℝ} {U : Set (Vec d)} (v η : Vec d → ℝ)
    {p ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε) (n : ℕ) :
    (∫⁻ x in U, ENNReal.ofReal (ρ x) * ‖η x * powG p ε n (v x)‖ₑ ^ (2 : ℝ)) ≤
    ENNReal.ofReal (2 + p / (p - 1)) *
      ∫⁻ x in U, ENNReal.ofReal (ρ x) * ENNReal.ofReal (η x ^ 2 * powF p ε n (v x)) := by
  have hp0 : 0 ≤ p := by linarith
  have hp1 : 0 ≤ p - 1 := by linarith
  have hK : 0 ≤ 2 + p / (p - 1) := by positivity
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro x
  dsimp only
  have hG := c5_powG_sq_le_powF hp hε n (v x)
  rw [Real.enorm_eq_ofReal_abs, ENNReal.rpow_two, ← ENNReal.ofReal_pow (abs_nonneg _)]
  have hpoint : (η x * powG p ε n (v x)) ^ 2 ≤
      (2 + p / (p - 1)) * (η x ^ 2 * powF p ε n (v x)) := by
    nlinarith [mul_le_mul_of_nonneg_left hG (sq_nonneg (η x))]
  calc
    ENNReal.ofReal (ρ x) * ENNReal.ofReal (|η x * powG p ε n (v x)| ^ 2) ≤
        ENNReal.ofReal (ρ x) * ENNReal.ofReal ((2 + p / (p - 1)) *
          (η x ^ 2 * powF p ε n (v x))) := by
      gcongr
      simpa only [sq_abs] using hpoint
    _ = _ := by rw [ENNReal.ofReal_mul hK]; ac_rfl

/-- Each signed slice mass is bounded by the same symmetric energy. -/
theorem c5_symmetric_truncated_power_slice_mass_le {d : ℕ}
    {ρ : Vec d → ℝ} {U : Set (Vec d)} (v η : Vec d → ℝ)
    {p ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε) (n : ℕ) :
    (∫⁻ x in U, ENNReal.ofReal (ρ x) * ‖η x * powG p ε n (v x)‖ₑ ^ (2 : ℝ)) ≤
    ENNReal.ofReal (2 + p / (p - 1)) *
      ∫⁻ x in U, ENNReal.ofReal (ρ x) *
        ENNReal.ofReal (η x ^ 2 * (powF p ε n (v x) + powF p ε n (-v x))) := by
  calc
    _ ≤ ENNReal.ofReal (2 + p / (p - 1)) *
        ∫⁻ x in U, ENNReal.ofReal (ρ x) * ENNReal.ofReal (η x ^ 2 * powF p ε n (v x)) :=
      c5_signed_truncated_power_slice_mass_le v η hp hε n
    _ ≤ _ := by
      gcongr
      exact le_add_of_nonneg_right (c5_all_real_truncated_power_structure hp hε n (-v x)).1

/-- The symmetric energy curvature controls either signed half-power derivative. -/
theorem c5_signed_powG_derivative_symmetric_curvature_bound {p ε : ℝ}
    (hp : 2 ≤ p) (hε : 0 < ε) (n : ℕ) (s : ℝ) :
    let f := powF p ε (n : ℝ)
    let F := fun y => f y + f (-y) - 2 * f 0
    (deriv (powG p ε n) s) ^ 2 ≤
      (2 + p / (p - 1)) * deriv (deriv F) s := by
  dsimp only
  let f := powF p ε (n : ℝ)
  have hf : ContDiff ℝ 2 f := powF_contDiff hε (Nat.cast_nonneg n)
  have hf' : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hdf : Differentiable ℝ (deriv f) :=
    (PDE.Parabolic.Chain.contDiff_deriv_of_two hf).differentiable (by norm_num)
  have hfirst : deriv (fun y => f y + f (-y) - 2 * f 0) =
      (fun y => deriv f y - deriv f (-y)) := by
    funext y
    change deriv (f + (f ∘ Neg.neg) - (fun _ => 2 * f 0)) y = _
    rw [deriv_sub (hf'.add (hf'.comp differentiable_neg)).differentiableAt
      (differentiableAt_const _), deriv_add hf'.differentiableAt
      (hf'.comp differentiable_neg).differentiableAt]
    change deriv f y + deriv (fun z => f (-z)) y - deriv (fun _ => 2 * f 0) y = _
    rw [deriv_comp_neg, deriv_const]
    ring
  have hsecond : deriv (deriv (fun y => f y + f (-y) - 2 * f 0)) s =
      deriv (deriv f) s + deriv (deriv f) (-s) := by
    rw [hfirst]
    change deriv (deriv f - (deriv f ∘ Neg.neg)) s = _
    rw [deriv_sub hdf.differentiableAt (hdf.comp differentiable_neg).differentiableAt]
    change deriv (deriv f) s - deriv (fun y => deriv f (-y)) s = _
    rw [deriv_comp_neg, sub_neg_eq_add]
  rw [hsecond]
  exact c5_signed_powG_derivative_curvature_bound hp hε n s

/-- The signed cutoff gradient is controlled by the symmetric truncated energy. -/
theorem c5_signed_truncated_power_cutoff_energy_pointwise {d : ℕ} {κ : ℝ}
    (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hc : IsUniformlyElliptic κ ρ α) {p ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε)
    (n : ℕ) (s : ℝ) (x G P : Vec d) (η : ℝ) :
    let F := fun y => powF p ε n y + powF p ε n (-y) - 2 * powF p ε n 0
    dot ((α x).mulVec
      (η • (deriv (powG p ε n) s • G) + powG p ε n s • P))
      (η • (deriv (powG p ε n) s • G) + powG p ε n s • P) ≤
      2 * κ⁻¹ * (2 + p / (p - 1)) *
        (η ^ 2 * deriv (deriv F) s * euclideanSq G +
          (powF p ε n s + powF p ε n (-s)) * euclideanSq P) := by
  dsimp only
  have hg := c5_powG_sq_le_powF hp hε n s
  have hf := (c5_all_real_truncated_power_structure hp hε n (-s)).1
  have hp0 : 0 ≤ p := by linarith
  have hp1 : 0 ≤ p - 1 := by linarith
  have hK : 0 ≤ 2 + p / (p - 1) := by positivity
  have hg' : powG p ε n s ^ 2 ≤
      (2 + p / (p - 1)) * (powF p ε n s + powF p ε n (-s)) := by
    nlinarith [mul_nonneg hK hf]
  exact c11_weighted_cutoff_chain_energy_pointwise hκ hc x G P η
    (powG p ε n s) (deriv (powG p ε n) s)
    (powF p ε n s + powF p ε n (-s))
    (deriv (deriv (fun y => powF p ε n y + powF p ε n (-y) -
      2 * powF p ε n 0)) s) (2 + p / (p - 1)) hg'
    (c5_signed_powG_derivative_symmetric_curvature_bound hp hε n s)

/-- Weighted cutoff bounds for both signs imply the absolute moment bound. -/
theorem c5_signed_cutoff_powG_weighted_moment_bound {d : ℕ} {κ : ℝ}
    (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hcoeff : IsUniformlyElliptic κ ρ α)
    {I : Set ℝ} {U : Set (Vec d)} {u η : ℝ × Vec d → ℝ}
    {G : ℝ × Vec d → Vec d} (hcal : IsWeightedCaloric ρ α I U u G)
    (S : Set (ℝ × Vec d)) (hS : MeasurableSet S) (hSV : S ⊆ I ×ˢ U)
    (hη : Continuous η) (hηone : ∀ z ∈ S, η z = 1)
    (p ε : ℝ) (hp : 2 ≤ p) (hε : 0 < ε) (B : ℝ≥0∞)
    (hbound : ∀ n : ℕ,
      (∫⁻ t in I, ∫⁻ x in U, ENNReal.ofReal (ρ x) *
        ‖η (t,x) * powG p ε n (u (t,x))‖ₑ ^ (2 * ((d : ℝ) + 2) / d)) ≤ B ∧
      (∫⁻ t in I, ∫⁻ x in U, ENNReal.ofReal (ρ x) *
        ‖η (t,x) * powG p ε n (-u (t,x))‖ₑ ^ (2 * ((d : ℝ) + 2) / d)) ≤ B) :
    (∫⁻ z in S, ENNReal.ofReal (|u z| + ε) ^ (p * (((d : ℝ) + 2) / d))) ≤
      ENNReal.ofReal κ⁻¹ * B + ENNReal.ofReal κ⁻¹ * B := by
  apply c5_signed_cutoff_powG_moment_bound hcal S hS hSV η hηone p ε hp hε
  intro n
  let q : ℝ := 2 * ((d : ℝ) + 2) / d
  let f : ℝ × Vec d → ℝ≥0∞ := fun z => ENNReal.ofReal |η z * powG p ε n (u z)| ^ q
  let g : ℝ × Vec d → ℝ≥0∞ := fun z => ENNReal.ofReal |η z * powG p ε n (-u z)| ^ q
  have hg : Continuous (powG p ε n) := (powG_contDiff hε (Nat.cast_nonneg n)).continuous
  have hf : AEMeasurable f (volume.restrict (I ×ˢ U)) :=
    (ENNReal.measurable_ofReal.comp_aemeasurable
      ((hη.aemeasurable.mul (hg.measurable.comp_aemeasurable hcal.1.aemeasurable)).abs)).pow_const q
  have hneg := c11_weighted_caloric_neg hcal
  have hb₁ : (∫⁻ z in I ×ˢ U, f z) ≤ ENNReal.ofReal κ⁻¹ * B := by
    calc
      _ ≤ ENNReal.ofReal κ⁻¹ * ∫⁻ z in I ×ˢ U, ENNReal.ofReal (ρ z.2) * f z :=
        (c8_density_lintegral_bounds (volume.restrict (I ×ˢ U)) κ hκ (fun z => ρ z.2)
          (fun z => ⟨(hcoeff.2.2 z.2).1, (hcoeff.2.2 z.2).2.1⟩) f).2
      _ ≤ ENNReal.ofReal κ⁻¹ * B := by
        rw [c11_weighted_caloric_cutoff_lintegral_prod hcoeff hcal hη hg]
        gcongr
        exact (hbound n).1
  have hb₂ : (∫⁻ z in I ×ˢ U, g z) ≤ ENNReal.ofReal κ⁻¹ * B := by
    calc
      _ ≤ ENNReal.ofReal κ⁻¹ * ∫⁻ z in I ×ˢ U, ENNReal.ofReal (ρ z.2) * g z :=
        (c8_density_lintegral_bounds (volume.restrict (I ×ˢ U)) κ hκ (fun z => ρ z.2)
          (fun z => ⟨(hcoeff.2.2 z.2).1, (hcoeff.2.2 z.2).2.1⟩) g).2
      _ ≤ ENNReal.ofReal κ⁻¹ * B := by
        rw [c11_weighted_caloric_cutoff_lintegral_prod hcoeff hneg hη hg]
        gcongr
        exact (hbound n).2
  change (∫⁻ z in I ×ˢ U, f z + g z) ≤ _
  rw [lintegral_add_left' hf]
  exact add_le_add hb₁ hb₂

/-- Applying weighted cutoff Sobolev to both signed truncations gives an
absolute moment bound from their slice mass and coefficient energies. -/
theorem c5_signed_cutoff_powG_sobolev_gain (d : ℕ) (hd : 2 ≤ d)
    (κ : ℝ) (hκ : 0 < κ) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d),
    IsUniformlyElliptic κ ρ α → ∀ (I : Set ℝ) (U : Set (Vec d)),
    MeasurableSet I → IsOpen U → volume (I ×ˢ U) < ∞ →
    ∀ (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d),
    IsWeightedCaloric ρ α I U u G →
    ∀ (η : ℝ × Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
    (∀ᵐ t ∂volume.restrict I, IsSpatialTest U (fun x => η (t,x))) →
    ∀ K : Set (Vec d), IsCompact K → K ⊆ U →
    (∀ t x, x ∉ K → η (t,x) = 0) →
    ∀ S : Set (ℝ × Vec d), MeasurableSet S → S ⊆ I ×ˢ U →
    (∀ z ∈ S, η z = 1) → ∀ p ε : ℝ, 2 ≤ p → 0 < ε →
    ∀ A E : ℝ≥0∞,
    (∀ (n : ℕ) (v : ℝ × Vec d → ℝ), (v = u ∨ v = fun z => -u z) →
      ∀ᵐ t ∂volume.restrict I,
      (∫⁻ x in U, ENNReal.ofReal (ρ x) *
        ‖η (t,x) * powG p ε n (v (t,x))‖ₑ ^ (2 : ℝ)) ≤ A) →
    (∀ (n : ℕ) (v : ℝ × Vec d → ℝ) (H : ℝ × Vec d → Vec d),
      ((v = u ∧ H = G) ∨ (v = (fun z => -u z) ∧ H = (fun z => -G z))) →
      (∫⁻ t in I, ∫⁻ x in U, ENNReal.ofReal
        (dot ((α x).mulVec
          (η (t,x) • (deriv (powG p ε n) (v (t,x)) • H (t,x)) +
            powG p ε n (v (t,x)) • (fun j => fderiv ℝ η (t,x) (0, unitVector j))))
          (η (t,x) • (deriv (powG p ε n) (v (t,x)) • H (t,x)) +
            powG p ε n (v (t,x)) • (fun j => fderiv ℝ η (t,x) (0, unitVector j))))) ≤ E) →
    (∫⁻ z in S, ENNReal.ofReal (|u z| + ε) ^ (p * (((d : ℝ) + 2) / d))) ≤
      ENNReal.ofReal κ⁻¹ * (C * A ^ (2 / (d : ℝ)) * E) +
      ENNReal.ofReal κ⁻¹ * (C * A ^ (2 / (d : ℝ)) * E) := by
  obtain ⟨C, hC, hsob⟩ := c11_weighted_caloric_spacetime_cutoff_chain_sobolev d hd κ hκ
  refine ⟨C, hC, ?_⟩
  intro ρ α hcoeff I U hI hU hfinite u G hcal η hη hcη htest K hK hKU hzero S hS hSV hηone p ε hp hε A E hmass henergy
  apply c5_signed_cutoff_powG_weighted_moment_bound hκ hcoeff hcal S hS hSV
    hη.continuous hηone p ε hp hε (C * A ^ (2 / (d : ℝ)) * E)
  intro n
  obtain ⟨M, hM, hdM⟩ := exists_powG1_bound (by linarith : 1 < p) hε (Nat.cast_nonneg n)
  have hF : ContDiff ℝ 1 (powG p ε n) := powG_contDiff hε (Nat.cast_nonneg n)
  constructor
  · have h := hsob ρ α hcoeff I U hI hU hfinite u G hcal (powG p ε n) hF M hM hdM
      η hη hcη htest K hK hKU hzero A (hmass n u (Or.inl rfl))
    refine h.trans ?_
    gcongr
    exact henergy n u G (Or.inl ⟨rfl, rfl⟩)
  · have h := hsob ρ α hcoeff I U hI hU hfinite (fun z => -u z) (fun z => -G z)
      (c11_weighted_caloric_neg hcal) (powG p ε n) hF M hM hdM
      η hη hcη htest K hK hKU hzero A (hmass n (fun z => -u z) (Or.inr rfl))
    refine h.trans ?_
    gcongr
    exact henergy n (fun z => -u z) (fun z => -G z) (Or.inr ⟨rfl, rfl⟩)

/-- A regularized absolute-moment estimate, with arbitrary additive slack,
passes to the unregularized norm. -/
theorem c5_signed_regularized_moment_to_eLpNorm {d : ℕ}
    (hd : 2 ≤ d) (C : ℝ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hcal : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G)
    (p : ℝ) (hp : 2 ≤ p)
    (hbound : ∀ δ : ℝ≥0, 0 < δ → ∃ ε : ℝ, 0 < ε ∧
      (∫⁻ z in Set.Ioo (-(1/4:ℝ)) (1/4) ×ˢ sourceBall 0 (1/2),
        ENNReal.ofReal (|u z| + ε) ^ (p * (((d:ℝ)+2)/d))) ≤
      (ENNReal.ofReal (Real.rpow (C*p^2) (1/p)) *
        eLpNorm u (ENNReal.ofReal p)
          (volume.restrict (Set.Ioo (-1:ℝ) 1 ×ˢ sourceBall 0 1))) ^
            (p * (((d:ℝ)+2)/d)) + δ) :
    eLpNorm u (ENNReal.ofReal (p*((d:ℝ)+2)/d))
      (volume.restrict (Set.Ioo (-(1/4:ℝ)) (1/4) ×ˢ sourceBall 0 (1/2))) ≤
    ENNReal.ofReal (Real.rpow (C*p^2) (1/p)) *
      eLpNorm u (ENNReal.ofReal p)
        (volume.restrict (Set.Ioo (-1:ℝ) 1 ×ˢ sourceBall 0 1)) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hp0 : 0 < p := by linarith
  have hq : 0 < p*((d:ℝ)+2)/d := by positivity
  have hsub : Set.Ioo (-(1/4:ℝ)) (1/4) ×ˢ sourceBall (0 : Vec d) (1/2) ⊆
      Set.Ioo (-1:ℝ) 1 ×ˢ sourceBall 0 1 := by
    rintro ⟨t,x⟩ ⟨ht,hx⟩
    constructor
    · constructor <;> linarith [ht.1, ht.2]
    · change euclideanNorm (x - 0) < 1/2 at hx
      change euclideanNorm (x - 0) < 1
      linarith
  have hu := hcal.1.aestronglyMeasurable.mono_measure (Measure.restrict_mono_set volume hsub)
  have hm : (∫⁻ z in Set.Ioo (-(1/4:ℝ)) (1/4) ×ˢ sourceBall (0 : Vec d) (1/2),
      ‖u z‖ₑ ^ (p*((d:ℝ)+2)/d)) ≤
      (ENNReal.ofReal (Real.rpow (C*p^2) (1/p)) *
        eLpNorm u (ENNReal.ofReal p)
          (volume.restrict (Set.Ioo (-1:ℝ) 1 ×ˢ sourceBall 0 1))) ^
            (p*((d:ℝ)+2)/d) := by
    apply ENNReal.le_of_forall_pos_le_add
    intro δ hδ _
    obtain ⟨ε, hε, hb⟩ := hbound δ hδ
    have heq : p * (((d:ℝ)+2)/d) = p*((d:ℝ)+2)/d := by ring
    rw [heq] at hb
    calc
      _ ≤ ∫⁻ z in Set.Ioo (-(1/4:ℝ)) (1/4) ×ˢ sourceBall (0 : Vec d) (1/2),
          ENNReal.ofReal (|u z| + ε) ^ (p*((d:ℝ)+2)/d) := by
        apply lintegral_mono
        intro z
        change ‖u z‖ₑ ^ (p*((d:ℝ)+2)/d) ≤
          ENNReal.ofReal (|u z| + ε) ^ (p*((d:ℝ)+2)/d)
        rw [Real.enorm_eq_ofReal_abs]
        exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (by linarith)) hq.le
      _ ≤ _ := hb
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ENNReal.ofReal_pos.mpr hq).ne' ENNReal.ofReal_ne_top hu,
    ENNReal.toReal_ofReal hq.le]
  have hr := ENNReal.rpow_le_rpow hm (by positivity : 0 ≤ 1 / (p*((d:ℝ)+2)/d))
  simpa only [← ENNReal.rpow_mul, mul_one_div_cancel hq.ne', ENNReal.rpow_one] using hr

/-- Conditional unit-cylinder gain: a uniform bound for the actual symmetric
truncations supplies the missing quantitative energy and Sobolev estimate. -/
theorem c5_native_signed_unit_moment_gain_of_truncation_bound
    (d : ℕ) (hd : 2 ≤ d)
    (C : ℝ)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : IsWeightedCaloric ρ α (Set.Ioo (-1) 1) (sourceBall 0 1) u G)
    (p : ℝ) (hp : 2 ≤ p)
    (hbound : ∀ δ : ℝ≥0, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ∀ n : ℕ,
      (∫⁻ z in Set.Ioo (-(1/4:ℝ)) (1/4) ×ˢ sourceBall 0 (1/2),
        ENNReal.ofReal (powF (p*((d:ℝ)+2)/d) ε (n:ℝ) (u z) +
          powF (p*((d:ℝ)+2)/d) ε (n:ℝ) (-u z))) ≤
      (ENNReal.ofReal (Real.rpow (C*p^2) (1/p)) *
        eLpNorm u (ENNReal.ofReal p)
          (volume.restrict (Set.Ioo (-1:ℝ) 1 ×ˢ sourceBall 0 1))) ^
            (p*((d:ℝ)+2)/d) + δ) :
    eLpNorm u (ENNReal.ofReal (p*((d:ℝ)+2)/d))
      (volume.restrict (Set.Ioo (-(1/4:ℝ)) (1/4) ×ˢ sourceBall 0 (1/2))) ≤
    ENNReal.ofReal (Real.rpow (C*p^2) (1/p)) *
      eLpNorm u (ENNReal.ofReal p)
        (volume.restrict (Set.Ioo (-1:ℝ) 1 ×ˢ sourceBall 0 1)) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hq : 2 ≤ p*((d:ℝ)+2)/d := by
    apply (le_div_iff₀ hd0).2
    nlinarith [mul_nonneg (show 0 ≤ p - 2 by linarith) hd0.le]
  have hsub : Set.Ioo (-(1/4:ℝ)) (1/4) ×ˢ sourceBall (0 : Vec d) (1/2) ⊆
      Set.Ioo (-1:ℝ) 1 ×ˢ sourceBall 0 1 := by
    rintro ⟨t,x⟩ ⟨ht,hx⟩
    constructor
    · constructor <;> linarith [ht.1, ht.2]
    · change euclideanNorm (x - 0) < 1/2 at hx
      change euclideanNorm (x - 0) < 1
      linarith
  have hu := hcal.1.aestronglyMeasurable.mono_measure (Measure.restrict_mono_set volume hsub)
  have hm : (∫⁻ z in Set.Ioo (-(1/4:ℝ)) (1/4) ×ˢ sourceBall (0 : Vec d) (1/2),
      ENNReal.ofReal (Real.rpow |u z| (p*((d:ℝ)+2)/d))) ≤
      (ENNReal.ofReal (Real.rpow (C*p^2) (1/p)) *
        eLpNorm u (ENNReal.ofReal p)
          (volume.restrict (Set.Ioo (-1:ℝ) 1 ×ˢ sourceBall 0 1))) ^
            (p*((d:ℝ)+2)/d) := by
    apply ENNReal.le_of_forall_pos_le_add
    intro δ hδ _
    obtain ⟨ε, hε, hb⟩ := hbound δ hδ
    exact c5_signed_moment_bound_of_symmetric_truncations _ u hu _ ε hq hε _ hb
  have hq0 : 0 < p*((d:ℝ)+2)/d := by linarith
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ENNReal.ofReal_pos.mpr hq0).ne' ENNReal.ofReal_ne_top hu,
    ENNReal.toReal_ofReal hq0.le]
  have hm' : (∫⁻ z in Set.Ioo (-(1/4:ℝ)) (1/4) ×ˢ sourceBall (0 : Vec d) (1/2),
      ‖u z‖ₑ ^ (p*((d:ℝ)+2)/d)) ≤
      (ENNReal.ofReal (Real.rpow (C*p^2) (1/p)) *
        eLpNorm u (ENNReal.ofReal p)
          (volume.restrict (Set.Ioo (-1:ℝ) 1 ×ˢ sourceBall 0 1))) ^
            (p*((d:ℝ)+2)/d) := by
    simpa [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_rpow_of_nonneg
      (abs_nonneg _) hq0.le] using hm
  have hr := ENNReal.rpow_le_rpow hm' (by positivity : 0 ≤ 1 / (p*((d:ℝ)+2)/d))
  simpa only [← ENNReal.rpow_mul, mul_one_div_cancel hq0.ne', ENNReal.rpow_one] using hr

/-- The coefficient in the signed truncation estimates is uniform for
exponents at least two. -/
theorem c5_signed_truncation_coefficient_le_four {p : ℝ} (hp : 2 ≤ p) :
    2 + p / (p - 1) ≤ 4 := by
  have hden : 0 < p - 1 := by linarith
  have hratio : p / (p - 1) ≤ 2 := (div_le_iff₀ hden).2 (by linarith)
  linarith

/-- The centered symmetric energy is nonnegative by convexity of the
truncated power. -/
theorem c5_symmetric_truncated_centered_power_nonneg {p ε : ℝ}
    (hp : 2 ≤ p) (hε : 0 < ε) (n : ℕ) (s : ℝ) :
    0 ≤ powF p ε (n : ℝ) s + powF p ε (n : ℝ) (-s) -
      2 * powF p ε (n : ℝ) 0 := by
  let f := powF p ε (n : ℝ)
  have hf : ContDiff ℝ 2 f := powF_contDiff hε (Nat.cast_nonneg n)
  have hdf : Differentiable ℝ (deriv f) :=
    (PDE.Parabolic.Chain.contDiff_deriv_of_two hf).differentiable (by norm_num)
  have hconv : ConvexOn ℝ Set.univ f := by
    apply convexOn_of_deriv2_nonneg' convex_univ
      (hf.differentiable (by norm_num)).differentiableOn hdf.differentiableOn
    intro x _
    simpa [Function.iterate_succ_apply] using
      (c5_all_real_truncated_power_structure hp hε n x).2.1
  have hmid := hconv.2 (Set.mem_univ s) (Set.mem_univ (-s))
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  dsimp only [smul_eq_mul] at hmid
  have hzero : (1 / 2 : ℝ) * s + (1 / 2 : ℝ) * -s = 0 := by ring
  rw [hzero] at hmid
  dsimp [f] at hmid
  linarith

/-- Nonnegative weights preserve nonnegativity of the centered energy. -/
theorem c5_symmetric_centered_energy_integral_nonneg
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (u w : X → ℝ)
    {p ε : ℝ} (hp : 2 ≤ p) (hε : 0 < ε) (n : ℕ)
    (hw : ∀ x, 0 ≤ w x) :
    0 ≤ ∫ x, w x * (powF p ε (n : ℝ) (u x) +
      powF p ε (n : ℝ) (-u x) - 2 * powF p ε (n : ℝ) 0) ∂μ := by
  apply integral_nonneg
  intro x
  exact mul_nonneg (hw x)
    (c5_symmetric_truncated_centered_power_nonneg hp hε n (u x))

/-- The symmetric energy curvature is nonnegative at every signed value. -/
theorem c5_symmetric_truncated_energy_curvature_nonneg {p ε : ℝ}
    (hp : 2 ≤ p) (hε : 0 < ε) (n : ℕ) (s : ℝ) :
    0 ≤ deriv (deriv (fun y => powF p ε (n : ℝ) y +
      powF p ε (n : ℝ) (-y) - 2 * powF p ε (n : ℝ) 0)) s := by
  let f := powF p ε (n : ℝ)
  have hf : ContDiff ℝ 2 f := powF_contDiff hε (Nat.cast_nonneg n)
  have hf' : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hdf : Differentiable ℝ (deriv f) :=
    (PDE.Parabolic.Chain.contDiff_deriv_of_two hf).differentiable (by norm_num)
  have hfirst : deriv (fun y => f y + f (-y) - 2 * f 0) =
      (fun y => deriv f y - deriv f (-y)) := by
    funext y
    change deriv (f + (f ∘ Neg.neg) - (fun _ => 2 * f 0)) y = _
    rw [deriv_sub (hf'.add (hf'.comp differentiable_neg)).differentiableAt
      (differentiableAt_const _), deriv_add hf'.differentiableAt
      (hf'.comp differentiable_neg).differentiableAt]
    change deriv f y + deriv (fun z => f (-z)) y - deriv (fun _ => 2 * f 0) y = _
    rw [deriv_comp_neg, deriv_const]
    ring
  change 0 ≤ deriv (deriv (fun y => f y + f (-y) - 2 * f 0)) s
  rw [hfirst]
  change 0 ≤ deriv (deriv f - (deriv f ∘ Neg.neg)) s
  rw [deriv_sub hdf.differentiableAt (hdf.comp differentiable_neg).differentiableAt]
  change 0 ≤ deriv (deriv f) s - deriv (fun y => deriv f (-y)) s
  rw [deriv_comp_neg, sub_neg_eq_add]
  exact add_nonneg (c5_all_real_truncated_power_structure hp hε n s).2.1
    (c5_all_real_truncated_power_structure hp hε n (-s)).2.1

/-- The dissipation density in the integrated signed energy inequality is
nonnegative. -/
theorem c5_signed_truncation_dissipation_nonneg {d : ℕ} {κ p ε : ℝ}
    (hκ : 0 < κ) (hp : 2 ≤ p) (hε : 0 < ε) (n : ℕ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (x G : Vec d) (s χ : ℝ) :
    0 ≤ χ ^ 2 * deriv (deriv (fun y => powF p ε (n : ℝ) y +
      powF p ε (n : ℝ) (-y) - 2 * powF p ε (n : ℝ) 0)) s *
      dot G ((α x).mulVec G) := by
  have hQ : 0 ≤ dot G ((α x).mulVec G) := by
    have he := (hell.2.2 x).2.2.2 G |>.1
    change κ * euclideanSq G ≤ dot G ((α x).mulVec G) at he
    exact (mul_nonneg hκ.le (PDE.vecNormSq_nonneg G)).trans he
  exact mul_nonneg (mul_nonneg (sq_nonneg χ)
    (c5_symmetric_truncated_energy_curvature_nonneg hp hε n s)) hQ

/-- Spatial integration preserves nonnegativity of signed dissipation. -/
theorem c5_signed_truncation_spatial_dissipation_nonneg {d : ℕ} {κ p ε : ℝ}
    (hκ : 0 < κ) (hp : 2 ≤ p) (hε : 0 < ε) (n : ℕ)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} (hell : IsUniformlyElliptic κ ρ α)
    (U : Set (Vec d)) (u χ : Vec d → ℝ) (G : Vec d → Vec d) :
    0 ≤ ∫ x in U, χ x ^ 2 * deriv (deriv (fun y => powF p ε (n : ℝ) y +
      powF p ε (n : ℝ) (-y) - 2 * powF p ε (n : ℝ) 0)) (u x) *
      dot (G x) ((α x).mulVec (G x)) := by
  apply integral_nonneg
  intro x
  exact c5_signed_truncation_dissipation_nonneg hκ hp hε n hell x (G x) (u x) (χ x)

/-- A signed truncation energy inequality controls the energy and the actual
nonnegative dissipation from one early time. -/
theorem c5_signed_truncation_energy_dissipation_of_average
    {d : ℕ} {κ p ε : ℝ} (hκ : 0 < κ) (hp : 2 ≤ p) (hε : 0 < ε)
    (n : ℕ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α)
    (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d) (χ : Vec d → ℝ)
    (E : ℝ → ℝ) (F : ℝ → ℝ → ℝ) (M A : ℝ) (hA : 0 ≤ A)
    (hE : IntegrableOn E (Set.Ioo (-1 : ℝ) (-1/2)))
    (havg : (∫ q in Set.Ioo (-1 : ℝ) (-1/2), E q) ≤ M)
    (henergy : ∀ s ∈ Set.Ioo (-1 : ℝ) (-1/2),
      ∀ t ∈ Set.Ioo (-1/4 : ℝ) (1/4),
      E t + (1/2 : ℝ) * (∫ q in s..t, ∫ x in sourceBall 0 1,
        χ x ^ 2 * deriv (deriv (fun y => powF p ε (n : ℝ) y +
          powF p ε (n : ℝ) (-y) - 2 * powF p ε (n : ℝ) 0)) (u (q,x)) *
          dot (G (q,x)) ((α x).mulVec (G (q,x)))) ≤ E s + A * F s t)
    (hforce : ∀ s ∈ Set.Ioo (-1 : ℝ) (-1/2),
      ∀ t ∈ Set.Ioo (-1/4 : ℝ) (1/4), F s t ≤ M)
    (hEpos : ∀ t ∈ Set.Ioo (-1/4 : ℝ) (1/4), 0 ≤ E t) :
    ∃ s ∈ Set.Ioo (-1 : ℝ) (-1/2), ∀ t ∈ Set.Ioo (-1/4 : ℝ) (1/4),
      E t ≤ (2 + A) * M ∧
      (∫ q in s..t, ∫ x in sourceBall 0 1,
        χ x ^ 2 * deriv (deriv (fun y => powF p ε (n : ℝ) y +
          powF p ε (n : ℝ) (-y) - 2 * powF p ε (n : ℝ) 0)) (u (q,x)) *
          dot (G (q,x)) ((α x).mulVec (G (q,x)))) ≤ 2 * ((2 + A) * M) := by
  let D : ℝ → ℝ → ℝ := fun s t => ∫ q in s..t, ∫ x in sourceBall 0 1,
    χ x ^ 2 * deriv (deriv (fun y => powF p ε (n : ℝ) y +
      powF p ε (n : ℝ) (-y) - 2 * powF p ε (n : ℝ) 0)) (u (q,x)) *
      dot (G (q,x)) ((α x).mulVec (G (q,x)))
  obtain ⟨s, hs, _, hout⟩ := c5_interval_energy_and_dissipation_of_average
    (a := (-1 : ℝ)) (b := -1/2) (c := -1/4) (d := 1/4) (by norm_num)
    E D F (fun _ => True) M A hA hE (ae_of_all _ fun _ => trivial) havg
    (fun s hs _ t ht => henergy s hs t ht)
    (fun s hs _ t ht => hforce s hs t ht) (by
      intro s hs _ t ht
      refine ⟨hEpos t ht, ?_⟩
      apply intervalIntegral.integral_nonneg (by linarith [hs.2, ht.1])
      intro q _
      exact c5_signed_truncation_spatial_dissipation_nonneg hκ hp hε n hell _
        (fun x => u (q,x)) χ (fun x => G (q,x)))
  refine ⟨s, hs, ?_⟩
  intro t ht
  have h := hout t ht
  norm_num [D] at h ⊢
  exact h

end EinsteinFull.Calculus
