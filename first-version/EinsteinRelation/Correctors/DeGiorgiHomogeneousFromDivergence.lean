import Mathlib
import DeGiorgi.WeakFormulation.SolutionInterfaces
import DeGiorgi.SobolevSpace.WeakDerivatives
open MeasureTheory Filter
open scoped Topology ENNReal
namespace EinsteinRelation.Correctors

/-- Hölder pairing: an `L^q` function against a sequence that tends to zero in `L^p`,
with `p⁻¹ + q⁻¹ = 1`, gives integrals tending to zero. -/
private lemma tendsto_integral_mul_eLpNorm_zero
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ} {g : ℕ → α → ℝ} {p q : ℝ}
    (hpq : p⁻¹ + q⁻¹ = 1) (hp : 1 < p) (hq : 1 < q)
    (hf : MemLp f (ENNReal.ofReal q) μ)
    (hg : ∀ n, MemLp (g n) (ENNReal.ofReal p) μ)
    (hlim : Tendsto (fun n => eLpNorm (g n) (ENNReal.ofReal p) μ) atTop (nhds 0)) :
    Tendsto (fun n => ∫ x, f x * g n x ∂μ) atTop (nhds 0) := by
  have hpqR : p.HolderConjugate q := Real.holderConjugate_iff.mpr ⟨hp, hpq⟩
  let C : ℝ := MeasureTheory.lpNorm f (ENNReal.ofReal q) μ
  have hlim' : Tendsto (fun n => MeasureTheory.lpNorm (g n) (ENNReal.ofReal p) μ) atTop
      (nhds 0) := by
    have hlim_toReal :
        Tendsto (fun n => (eLpNorm (g n) (ENNReal.ofReal p) μ).toReal) atTop (nhds 0) :=
      (ENNReal.tendsto_toReal_zero_iff (fun n => (hg n).eLpNorm_ne_top)).2 hlim
    have hEq :
        (fun n => (eLpNorm (g n) (ENNReal.ofReal p) μ).toReal) =
          (fun n => MeasureTheory.lpNorm (g n) (ENNReal.ofReal p) μ) := by
      funext n
      simpa using
        (MeasureTheory.toReal_eLpNorm
          (μ := μ) (p := ENNReal.ofReal p) (f := g n) (hg n).aestronglyMeasurable)
    simpa [hEq] using hlim_toReal
  have hbound :
      ∀ n, |∫ x, f x * g n x ∂μ| ≤ C * MeasureTheory.lpNorm (g n) (ENNReal.ofReal p) μ := by
    intro n
    have h_int :
        |∫ x, f x * g n x ∂μ| ≤ ∫ x, ‖f x‖ * ‖g n x‖ ∂μ := by
      calc
        |∫ x, f x * g n x ∂μ| = ‖∫ x, f x * g n x ∂μ‖ := by rw [Real.norm_eq_abs]
        _ ≤ ∫ x, ‖f x * g n x‖ ∂μ := by
          simpa using norm_integral_le_integral_norm (μ := μ) (f := fun x => f x * g n x)
        _ = ∫ x, ‖f x‖ * ‖g n x‖ ∂μ := by simp_rw [norm_mul]
    have h_holder :=
      MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
        (μ := μ) (f := f) (g := g n) (p := q) (q := p) hpqR.symm hf (hg n)
    have hp0 : ENNReal.ofReal p ≠ 0 := by
      intro hp0'
      have : p ≤ 0 := by simpa [ENNReal.ofReal_eq_zero] using hp0'
      linarith
    have hq0 : ENNReal.ofReal q ≠ 0 := by
      intro hq0'
      have : q ≤ 0 := by simpa [ENNReal.ofReal_eq_zero] using hq0'
      linarith
    have h_f_lp :
        MeasureTheory.lpNorm f (ENNReal.ofReal q) μ =
          (∫ x, ‖f x‖ ^ q ∂μ) ^ q⁻¹ := by
      simpa [ENNReal.toReal_ofReal (by linarith : 0 ≤ q)] using
        (MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
          (μ := μ) (p := ENNReal.ofReal q) (f := f) hq0 (by simp) hf.aestronglyMeasurable)
    have h_g_lp :
        MeasureTheory.lpNorm (g n) (ENNReal.ofReal p) μ =
          (∫ x, ‖g n x‖ ^ p ∂μ) ^ p⁻¹ := by
      simpa [ENNReal.toReal_ofReal (by linarith : 0 ≤ p)] using
        (MeasureTheory.lpNorm_eq_integral_norm_rpow_toReal
          (μ := μ) (p := ENNReal.ofReal p) (f := g n) hp0 (by simp)
          (hg n).aestronglyMeasurable)
    calc
      |∫ x, f x * g n x ∂μ| ≤ ∫ x, ‖f x‖ * ‖g n x‖ ∂μ := h_int
      _ ≤ C * MeasureTheory.lpNorm (g n) (ENNReal.ofReal p) μ := by
        simpa [C, h_f_lp, h_g_lp, mul_comm, mul_left_comm, mul_assoc] using h_holder
  have h_upper :
      Tendsto (fun n => C * MeasureTheory.lpNorm (g n) (ENNReal.ofReal p) μ) atTop (nhds 0) := by
    simpa using Tendsto.const_mul C hlim'
  have h_abs :
      Tendsto (fun n => |∫ x, f x * g n x ∂μ|) atTop (nhds 0) :=
    squeeze_zero (fun n => abs_nonneg _) hbound h_upper
  exact (tendsto_zero_iff_abs_tendsto_zero _).2 h_abs

/-- Coordinate derivatives of a smooth compactly supported function lie in `L²(Ω)`. -/
private lemma memLp_fderiv_single_two {d : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin d)))
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφc : HasCompactSupport φ) (i : Fin d) :
    MemLp (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) 2 (volume.restrict Ω) := by
  have hcont : Continuous (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hsupp : HasCompactSupport (fun x => fderiv ℝ φ x (EuclideanSpace.single i 1)) :=
    hφc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
  exact (hcont.memLp_of_hasCompactSupport hsupp).restrict Ω

/-- If `f ∈ L²(Ω)` and the coordinate derivatives `∂ᵢ ψₙ` converge to `g` in `L²(Ω)`, then
`∫_Ω f ∂ᵢψₙ` converges to `∫_Ω f g`. -/
private lemma tendsto_integral_mul_fderiv_single_two
    {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))} {f g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hf : MemLp f 2 (volume.restrict Ω)) (hg : MemLp g 2 (volume.restrict Ω))
    {ψ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ} (hψ_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (ψ n))
    (hψ_cpt : ∀ n, HasCompactSupport (ψ n)) (i : Fin d)
    (hψ_lim : Tendsto (fun n => eLpNorm
      (fun x => fderiv ℝ (ψ n) x (EuclideanSpace.single i 1) - g x) 2 (volume.restrict Ω))
      atTop (nhds 0)) :
    Tendsto (fun n => ∫ x in Ω, f x * fderiv ℝ (ψ n) x (EuclideanSpace.single i 1)) atTop
      (nhds (∫ x in Ω, f x * g x)) := by
  have hd_mem : ∀ n, MemLp (fun x => fderiv ℝ (ψ n) x (EuclideanSpace.single i 1)) 2
      (volume.restrict Ω) :=
    fun n => memLp_fderiv_single_two Ω (hψ_smooth n) (hψ_cpt n) i
  have hdiff_mem : ∀ n, MemLp
      (fun x => fderiv ℝ (ψ n) x (EuclideanSpace.single i 1) - g x) 2 (volume.restrict Ω) :=
    fun n => (hd_mem n).sub hg
  have hi_fg : Integrable (fun x => f x * g x) (volume.restrict Ω) :=
    hf.integrable_mul hg
  have hi_diff : ∀ n, Integrable
      (fun x => f x * (fderiv ℝ (ψ n) x (EuclideanSpace.single i 1) - g x))
      (volume.restrict Ω) :=
    fun n => hf.integrable_mul (hdiff_mem n)
  have hsplit : ∀ n, ∫ x in Ω, f x * fderiv ℝ (ψ n) x (EuclideanSpace.single i 1) =
      (∫ x in Ω, f x * g x) +
        ∫ x in Ω, f x * (fderiv ℝ (ψ n) x (EuclideanSpace.single i 1) - g x) := by
    intro n
    calc ∫ x in Ω, f x * fderiv ℝ (ψ n) x (EuclideanSpace.single i 1)
        = ∫ x in Ω, (f x * g x + f x * (fderiv ℝ (ψ n) x (EuclideanSpace.single i 1) - g x)) := by
          congr with x
          ring
      _ = (∫ x in Ω, f x * g x) +
            ∫ x in Ω, f x * (fderiv ℝ (ψ n) x (EuclideanSpace.single i 1) - g x) :=
          integral_add hi_fg (hi_diff n)
  have h2 : ENNReal.ofReal 2 = 2 := ENNReal.ofReal_ofNat 2
  have hholder : Tendsto (fun n =>
      ∫ x in Ω, f x * (fderiv ℝ (ψ n) x (EuclideanSpace.single i 1) - g x)) atTop (nhds 0) :=
    tendsto_integral_mul_eLpNorm_zero (μ := volume.restrict Ω) (f := f)
      (g := fun n x => fderiv ℝ (ψ n) x (EuclideanSpace.single i 1) - g x) (p := 2) (q := 2)
      (by norm_num) (by norm_num) (by norm_num)
      (by rw [h2]; exact hf)
      (fun n => by rw [h2]; exact hdiff_mem n)
      (by rw [h2]; exact hψ_lim)
  have hfin := Tendsto.const_add (∫ x in Ω, f x * g x) hholder
  rw [add_zero] at hfin
  exact Tendsto.congr (fun n => (hsplit n).symm) hfin

theorem isHomogeneousWeakSolution_of_hasWeakDiv {d : ℕ} [NeZero d]
    {Ω : Set (EuclideanSpace ℝ (Fin d))} (hΩ : IsOpen Ω)
    (A : DeGiorgi.EllipticCoeff d Ω) {K : ℝ}
    (hK : ∀ x ∈ Ω, ∀ i j, |A.a x i j| ≤ K)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} (hw : DeGiorgi.MemW1pWitness 2 u Ω)
    (hdiv : DeGiorgi.HasWeakDiv (fun _ => (0 : ℝ))
      (fun x => DeGiorgi.matMulE (A.a x) (hw.weakGrad x)) Ω) :
    DeGiorgi.IsHomogeneousWeakSolution A u := by
  refine ⟨hw.memW1p, fun hu φ hφ hφw => ?_⟩
  obtain ⟨_, hw0, ψ, hψ_smooth, hψ_cpt, hψ_sub, _, hψ_grad⟩ := hφ
  -- Each component of the flux `A ∇u` is an `L²(Ω)` function, by the entry bound `K`.
  have hF : ∀ i : Fin d, MemLp (fun x => DeGiorgi.matMulE (A.a x) (hw.weakGrad x) i) 2
      (volume.restrict Ω) := by
    intro i
    have hT : ∀ j : Fin d, MemLp (fun x => A.a x i j * hw.weakGrad x j) 2
        (volume.restrict Ω) := by
      intro j
      refine MemLp.of_le_mul (g := fun x => hw.weakGrad x j) (c := K)
        (hw.weakGrad_component_memLp j) ?_ ?_
      · exact (A.measurable_apply i j).aestronglyMeasurable.mul
          (hw.weakGrad_component_memLp j).aestronglyMeasurable
      · filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
        simp only [norm_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hK x hx i j) (abs_nonneg _)
    have hsum := memLp_finset_sum (Finset.univ : Finset (Fin d))
      (f := fun j x => A.a x i j * hw.weakGrad x j) (fun j _ => hT j)
    convert hsum using 1
  have hd_mem : ∀ (n : ℕ) (i : Fin d),
      MemLp (fun x => fderiv ℝ (ψ n) x (EuclideanSpace.single i 1)) 2 (volume.restrict Ω) :=
    fun n i => memLp_fderiv_single_two Ω (hψ_smooth n) (hψ_cpt n) i
  have hint0 : ∀ (n : ℕ) (i : Fin d), Integrable (fun x =>
      DeGiorgi.matMulE (A.a x) (hw.weakGrad x) i * fderiv ℝ (ψ n) x (EuclideanSpace.single i 1))
      (volume.restrict Ω) :=
    fun n i => (hF i).integrable_mul (hd_mem n i)
  have hint1 : ∀ i : Fin d, Integrable (fun x =>
      DeGiorgi.matMulE (A.a x) (hw.weakGrad x) i * hw0.weakGrad x i) (volume.restrict Ω) :=
    fun i => (hF i).integrable_mul (hw0.weakGrad_component_memLp i)
  -- The approximants `ψ n` are admissible tests in the divergence identity.
  have h0 : ∀ n : ℕ, (∑ i : Fin d, ∫ x in Ω,
      DeGiorgi.matMulE (A.a x) (hw.weakGrad x) i * fderiv ℝ (ψ n) x (EuclideanSpace.single i 1))
        = 0 := by
    intro n
    rw [← integral_finset_sum Finset.univ (fun i _ => hint0 n i)]
    exact (hdiv (ψ n) (hψ_smooth n) (hψ_cpt n) (hψ_sub n)).trans (by simp)
  have hlim : Tendsto (fun n : ℕ => ∑ i : Fin d, ∫ x in Ω,
      DeGiorgi.matMulE (A.a x) (hw.weakGrad x) i * fderiv ℝ (ψ n) x (EuclideanSpace.single i 1))
      atTop (nhds (∑ i : Fin d, ∫ x in Ω,
        DeGiorgi.matMulE (A.a x) (hw.weakGrad x) i * hw0.weakGrad x i)) :=
    tendsto_finset_sum Finset.univ fun i _ =>
      tendsto_integral_mul_fderiv_single_two (hF i) (hw0.weakGrad_component_memLp i)
        hψ_smooth hψ_cpt i (hψ_grad i)
  have hzero : Tendsto (fun n : ℕ => ∑ i : Fin d, ∫ x in Ω,
      DeGiorgi.matMulE (A.a x) (hw.weakGrad x) i * fderiv ℝ (ψ n) x (EuclideanSpace.single i 1))
      atTop (nhds 0) :=
    Tendsto.congr (fun n => (h0 n).symm) tendsto_const_nhds
  have hT0 : (∑ i : Fin d, ∫ x in Ω,
      DeGiorgi.matMulE (A.a x) (hw.weakGrad x) i * hw0.weakGrad x i) = 0 :=
    tendsto_nhds_unique hlim hzero
  -- The bilinear form against `φ` is the sum of the componentwise pairings.
  have hBil : DeGiorgi.bilinFormOfCoeff A hw hw0 = ∑ i : Fin d, ∫ x in Ω,
      DeGiorgi.matMulE (A.a x) (hw.weakGrad x) i * hw0.weakGrad x i := by
    rw [← integral_finset_sum Finset.univ (fun i _ => hint1 i)]
    unfold DeGiorgi.bilinFormOfCoeff
    refine integral_congr_ae ?_
    filter_upwards with x
    simp [DeGiorgi.bilinFormIntegrandOfCoeff, PiLp.inner_apply, DeGiorgi.matMulE_apply,
      Matrix.mulVec, dotProduct, mul_comm]
  rw [DeGiorgi.bilinFormOfCoeff_eq_right hΩ A hu hφw hw0,
    DeGiorgi.bilinFormOfCoeff_eq_left hΩ A hu hw hw0, hBil, hT0]

end EinsteinRelation.Correctors
