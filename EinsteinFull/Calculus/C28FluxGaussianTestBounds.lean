import EinsteinFull.Calculus.CarverSFluxBlockGain
import EinsteinFull.Calculus.C4PhysicalLocalEnergy
import EinsteinFull.Calculus.S1SharpBoundSupport

open MeasureTheory Set
open scoped BigOperators

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull

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


theorem c28_flux_cutoff_kernel_value_and_derivative_bound (d : ℕ) (D : StructuralData d) :
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
      ‖ψ y‖ ≤ Cder k * s ^ (-(k : ℝ) / 2) * W ∧
      ∀ j : Fin d, ‖fderiv ℝ ψ y (unitVector j)‖ ≤
        (Cder k * (R / r) * s ^ (-(k : ℝ) / 2) +
          Cder (k + 1) * s ^ (-((k + 1 : ℕ) : ℝ) / 2)) * W := by
  obtain ⟨Cenv, Cder, hCenv, hCder, hkernel⟩ :=
    carverS_flux_block_gaussian_envelope d D
  refine ⟨Cenv, Cder, hCenv, hCder, ?_⟩
  intro Q i r hr s hs χ hχ _hcompact R _hsupp hχabs hχgrad k dirs x z y hy ψ W
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hD (n : ℕ) : 0 ≤ Cder n := (zero_le_one.trans (hCder n))
  have hsup := carverS_flux_block_gaussian_spatial_sup s hs Cenv x z (R * r)
    (mul_nonneg hR hr.le)
  have hk : ‖iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i s hs 0) (x - y)
      (fun l => unitVector (dirs l))‖ ≤ Cder k * s ^ (-(k : ℝ) / 2) * W :=
    (hkernel Q i s hs k dirs (x - y)).trans
      (mul_le_mul_of_nonneg_left (hsup.2.2 y hy)
        (mul_nonneg (hD k) (Real.rpow_nonneg hs.le _)))
  constructor
  · change ‖(χ (y - z) : ℂ) *
      iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i s hs 0) (x - y)
        (fun l => unitVector (dirs l))‖ ≤ _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ 1 * (Cder k * s ^ (-(k : ℝ) / 2) * W) :=
        mul_le_mul (hχabs (y - z)) hk (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  · intro j
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


theorem c28_flux_cutoff_kernel_tsupport {d : ℕ} {Λ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ r₀) (i : Fin d) (r s : ℝ) (hr : 0 < r) (hs : 0 < s)
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hc : HasCompactSupport χ)
    (hsupp : Function.support χ ⊆ {y : Vec d | euclideanNorm y ≤ (2 * Real.sqrt (d : ℝ) + 2) * r})
    (k : ℕ) (dirs : Fin k → Fin d) (x z : Vec d) :
    let ψ : Vec d → ℂ := fun y => (χ (y-z) : ℂ) *
      iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i s hs 0) (x-y)
        (fun q => unitVector (dirs q))
    ContDiff ℝ (⊤ : ℕ∞) ψ ∧ HasCompactSupport ψ ∧
      tsupport ψ ⊆ {y : Vec d | euclideanNorm (y-z) < 2 * (2 * Real.sqrt (d : ℝ) + 2) * r} := by
  dsimp only
  have hcut : HasCompactSupport (fun y : Vec d => χ (y - z)) :=
    hc.comp_homeomorph (Homeomorph.subRight z)
  have hsupport : Function.support (fun y : Vec d => (χ (y-z) : ℂ) *
      iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i s hs 0) (x-y)
        (fun q => unitVector (dirs q))) ⊆ Function.support (fun y : Vec d => χ (y-z)) := by
    intro y hy
    simp only [Function.mem_support] at hy ⊢
    intro hz
    apply hy
    simp [hz]
  have hclosed : IsClosed {y : Vec d | euclideanNorm (y-z) ≤ (2 * Real.sqrt (d : ℝ) + 2) * r} :=
    isClosed_le (Entropy.continuous_euclideanNorm'.comp (continuous_id.sub continuous_const)) continuous_const
  have hsub : tsupport (fun y : Vec d => (χ (y-z) : ℂ) *
      iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i s hs 0) (x-y)
        (fun q => unitVector (dirs q))) ⊆
      {y : Vec d | euclideanNorm (y-z) ≤ (2 * Real.sqrt (d : ℝ) + 2) * r} := by
    apply closure_minimal _ hclosed
    intro y hy
    exact hsupp (hsupport hy)
  refine ⟨?_, hcut.mono hsupport, ?_⟩
  · apply contDiff_infty.mpr
    intro n
    have hk := (contDiff_homogenizedGaussianKernel_complexForce Q i s hs 0).iteratedFDeriv_right (i := k) (m := n) (by simp)
    have hx : ContDiff ℝ n (fun y : Vec d => x - y) := contDiff_const.sub contDiff_id
    have hχn : ContDiff ℝ n χ := hχ.of_le (by simp)
    exact (Complex.ofRealCLM.contDiff.comp (hχn.comp (contDiff_id.sub contDiff_const))).mul
      ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Vec d) ℂ
        (fun q => unitVector (dirs q))).contDiff.comp (hk.comp hx))
  · intro y hy
    have hR : 0 < (2 * Real.sqrt (d : ℝ) + 2) * r := by positivity
    have := hsub hy
    dsimp at this ⊢
    nlinarith


theorem c28_flux_cutoff_kernel_euclidean_derivative_bound (d : ℕ) (D : StructuralData d) :
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
      ‖ψ y‖ ≤ Cder k * s ^ (-(k : ℝ) / 2) * W ∧
      Real.sqrt (∑ j : Fin d, ‖fderiv ℝ ψ y (unitVector j)‖ ^ 2) ≤
        Real.sqrt (d : ℝ) * (Cder k * (R / r) * s ^ (-(k : ℝ) / 2) +
          Cder (k + 1) * s ^ (-((k + 1 : ℕ) : ℝ) / 2)) * W := by
  obtain ⟨Cenv, Cder, henv, hder, hbound⟩ :=
    c28_flux_cutoff_kernel_value_and_derivative_bound d D
  refine ⟨Cenv, Cder, henv, hder, ?_⟩
  intro Q i r hr s hs χ hχ hc R hsupp habs hgrad k dirs x z y hy ψ W
  obtain ⟨hv, hj⟩ := hbound Q i r hr s hs χ hχ hc hsupp habs hgrad k dirs x z y hy
  refine ⟨hv, ?_⟩
  let A := (Cder k * (R / r) * s ^ (-(k : ℝ) / 2) +
    Cder (k + 1) * s ^ (-((k + 1 : ℕ) : ℝ) / 2)) * W
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hW : 0 ≤ W := (carverS_flux_block_gaussian_spatial_sup s hs Cenv x z (R * r)
    (mul_nonneg hR hr.le)).2.1
  have hD (n : ℕ) : 0 ≤ Cder n := zero_le_one.trans (hder n)
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (add_nonneg
      (mul_nonneg (mul_nonneg (hD k) (div_nonneg hR hr.le)) (Real.rpow_nonneg hs.le _))
      (mul_nonneg (hD (k + 1)) (Real.rpow_nonneg hs.le _))) hW
  have hsum : (∑ j : Fin d, ‖fderiv ℝ ψ y (unitVector j)‖ ^ 2) ≤ (d : ℝ) * A ^ 2 := by
    calc
      _ ≤ ∑ _j : Fin d, A ^ 2 := Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hj j) 2)
      _ = (d : ℝ) * A ^ 2 := by simp
  calc
    _ ≤ Real.sqrt ((d : ℝ) * A ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (d : ℝ) * A := by rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq hA]
    _ = _ := by dsimp [A]; ring

theorem c28_flux_cutoff_kernel_global_euclidean_derivative_bound (d : ℕ) (D : StructuralData d) :
    ∃ Cenv : ℝ, ∃ Cder : ℕ → ℝ, 1 ≤ Cenv ∧ (∀ k, 1 ≤ Cder k) ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (i : Fin d)
      (r : ℝ) (_hr : 0 < r) (s : ℝ) (hs : 0 < s) (χ : Vec d → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
      let R := 2 * Real.sqrt (d : ℝ) + 2
      Function.support χ ⊆ {y : Vec d | euclideanNorm y ≤ R * r} →
      (∀ y, |χ y| ≤ 1) →
      (∀ y, Real.sqrt (∑ j : Fin d, (fderiv ℝ χ y (unitVector j)) ^ 2) ≤ R / r) →
      ∀ (k : ℕ) (dirs : Fin k → Fin d) (x z y : Vec d),
      let ψ : Vec d → ℂ := fun v => (χ (v - z) : ℂ) *
        iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i s hs 0) (x - v)
          (fun j => unitVector (dirs j))
      let W := sSup ((fun v : Vec d => s ^ (-(d : ℝ) / 2) *
        Real.exp (-euclideanNorm (x - v) ^ 2 / (Cenv * s))) ''
          {v : Vec d | euclideanNorm (v - z) ≤ R * r})
      ‖ψ y‖ ≤ Cder k * s ^ (-(k : ℝ) / 2) * W ∧
      Real.sqrt (∑ j : Fin d, ‖fderiv ℝ ψ y (unitVector j)‖ ^ 2) ≤
        Real.sqrt (d : ℝ) * (Cder k * (R / r) * s ^ (-(k : ℝ) / 2) +
          Cder (k + 1) * s ^ (-((k + 1 : ℕ) : ℝ) / 2)) * W := by
  obtain ⟨Cenv, Cder, henv, hder, hbound⟩ :=
    c28_flux_cutoff_kernel_euclidean_derivative_bound d D
  refine ⟨Cenv, Cder, henv, hder, ?_⟩
  intro Q i r hr s hs χ hχ hc R hsupp habs hgrad k dirs x z y ψ W
  by_cases hy : euclideanNorm (y - z) ≤ R * r
  · exact hbound Q i r hr s hs χ hχ hc hsupp habs hgrad k dirs x z y hy
  · have hclosed : IsClosed {v : Vec d | euclideanNorm (v-z) ≤ R*r} :=
      isClosed_le (Entropy.continuous_euclideanNorm'.comp (continuous_id.sub continuous_const)) continuous_const
    have hsub : tsupport ψ ⊆ {v : Vec d | euclideanNorm (v-z) ≤ R*r} := by
      apply closure_minimal _ hclosed
      intro v hv
      apply hsupp
      simp only [Function.mem_support] at hv ⊢
      intro hz
      apply hv
      simp [ψ, hz]
    have hnot : y ∉ tsupport ψ := fun h => hy (hsub h)
    have hψ : ψ y = 0 := image_eq_zero_of_notMem_tsupport hnot
    have hd : fderiv ℝ ψ y = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hnot (tsupport_fderiv_subset ℝ h))
    have hR : 0 ≤ R := by dsimp [R]; positivity
    have hW : 0 ≤ W := (carverS_flux_block_gaussian_spatial_sup s hs Cenv x z (R * r)
      (mul_nonneg hR hr.le)).2.1
    have hD (n : ℕ) : 0 ≤ Cder n := zero_le_one.trans (hder n)
    constructor
    · simpa [hψ] using mul_nonneg (mul_nonneg (hD k) (Real.rpow_nonneg hs.le _)) hW
    · have hnonneg := mul_nonneg (mul_nonneg (Real.sqrt_nonneg (d : ℝ)) (add_nonneg
        (mul_nonneg (mul_nonneg (hD k) (div_nonneg hR hr.le)) (Real.rpow_nonneg hs.le (-(k : ℝ) / 2)))
        (mul_nonneg (hD (k + 1)) (Real.rpow_nonneg hs.le (-((k + 1 : ℕ) : ℝ) / 2))))) hW
      simpa [hd] using hnonneg

theorem c28_flux_cutoff_kernel_integral_norm_bound (d : ℕ) (D : StructuralData d) :
    ∃ Cenv : ℝ, ∃ Cder : ℕ → ℝ, 1 ≤ Cenv ∧ (∀ k, 1 ≤ Cder k) ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (i : Fin d)
      (r : ℝ) (_hr : 0 < r) (s : ℝ) (hs : 0 < s) (χ : Vec d → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
      let R := 2 * Real.sqrt (d : ℝ) + 2
      Function.support χ ⊆ {y : Vec d | euclideanNorm y ≤ R * r} →
      (∀ y, |χ y| ≤ 1) →
      (∀ y, Real.sqrt (∑ j : Fin d, (fderiv ℝ χ y (unitVector j)) ^ 2) ≤ R / r) →
      ∀ (k : ℕ) (dirs : Fin k → Fin d) (x z : Vec d),
      let ψ : Vec d → ℂ := fun v => (χ (v - z) : ℂ) *
        iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i s hs 0) (x - v)
          (fun j => unitVector (dirs j))
      let W := sSup ((fun v : Vec d => s ^ (-(d : ℝ) / 2) *
        Real.exp (-euclideanNorm (x - v) ^ 2 / (Cenv * s))) ''
          {v : Vec d | euclideanNorm (v - z) ≤ R * r})
      Integrable ψ volume ∧
      (∫ y, ‖ψ y‖ ∂volume) ≤
        (volume {y : Vec d | euclideanNorm (y - z) ≤ R * r}).toReal *
          (Cder k * s ^ (-(k : ℝ) / 2) * W) := by
  obtain ⟨Cenv, Cder, henv, hder, hbound⟩ :=
    c28_flux_cutoff_kernel_global_euclidean_derivative_bound d D
  refine ⟨Cenv, Cder, henv, hder, ?_⟩
  intro Q i r hr s hs χ hχ hc R hsupp habs hgrad k dirs x z ψ W
  have hregular := c28_flux_cutoff_kernel_tsupport Q i r s hr hs χ hχ hc hsupp k dirs x z
  have hint : Integrable ψ volume := hregular.1.continuous.integrable_of_hasCompactSupport hregular.2.1
  refine ⟨hint, ?_⟩
  let K : Set (Vec d) := {y | euclideanNorm (y - z) ≤ R * r}
  let A : ℝ := Cder k * s ^ (-(k : ℝ) / 2) * W
  have hK : IsCompact K := isCompact_physical_euclidean_closedBall z (R * r)
  have hfinite : volume K ≠ ⊤ := ne_of_lt hK.measure_lt_top
  have hsub : Function.support ψ ⊆ K := by
    intro v hv
    apply hsupp
    simp only [Function.mem_support] at hv ⊢
    intro hz
    apply hv
    simp [ψ, hz]
  have hcomp : Integrable (K.indicator (fun _ : Vec d => A)) volume :=
    (integrableOn_const hfinite).integrable_indicator hK.measurableSet
  calc
    _ ≤ ∫ y, K.indicator (fun _ : Vec d => A) y ∂volume := by
      apply integral_mono_ae hint.norm hcomp
      filter_upwards with y
      by_cases hy : y ∈ K
      · rw [Set.indicator_of_mem hy]
        exact (hbound Q i r hr s hs χ hχ hc hsupp habs hgrad k dirs x z y).1
      · have hz : ψ y = 0 := by
          apply Function.notMem_support.mp
          exact fun h => hy (hsub h)
        simp [Set.indicator_of_notMem hy, hz]
    _ = _ := by rw [integral_indicator_const A hK.measurableSet]; simp [K, A, smul_eq_mul, Measure.real_def]


theorem c28_flux_cutoff_kernel_integral_gradient_norm_bound (d : ℕ) (D : StructuralData d) :
    ∃ Cenv : ℝ, ∃ Cder : ℕ → ℝ, 1 ≤ Cenv ∧ (∀ k, 1 ≤ Cder k) ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (i : Fin d)
      (r : ℝ) (_hr : 0 < r) (s : ℝ) (hs : 0 < s) (χ : Vec d → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
      let R := 2 * Real.sqrt (d : ℝ) + 2
      Function.support χ ⊆ {y : Vec d | euclideanNorm y ≤ R * r} →
      (∀ y, |χ y| ≤ 1) →
      (∀ y, Real.sqrt (∑ j : Fin d, (fderiv ℝ χ y (unitVector j)) ^ 2) ≤ R / r) →
      ∀ (k : ℕ) (dirs : Fin k → Fin d) (x z : Vec d),
      let ψ : Vec d → ℂ := fun v => (χ (v - z) : ℂ) *
        iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i s hs 0) (x - v)
          (fun j => unitVector (dirs j))
      let W := sSup ((fun v : Vec d => s ^ (-(d : ℝ) / 2) *
        Real.exp (-euclideanNorm (x - v) ^ 2 / (Cenv * s))) ''
          {v : Vec d | euclideanNorm (v - z) ≤ R * r})
      Integrable (fun y : Vec d =>
        Real.sqrt (∑ j : Fin d, ‖fderiv ℝ ψ y (unitVector j)‖ ^ 2)) volume ∧
      (∫ y : Vec d, Real.sqrt (∑ j : Fin d, ‖fderiv ℝ ψ y (unitVector j)‖ ^ 2) ∂volume) ≤
        (volume {y : Vec d | euclideanNorm (y - z) ≤ R * r}).toReal *
          (Real.sqrt (d : ℝ) * (Cder k * (R / r) * s ^ (-(k : ℝ) / 2) +
            Cder (k + 1) * s ^ (-((k + 1 : ℕ) : ℝ) / 2)) * W) := by
  obtain ⟨Cenv, Cder, henv, hder, hbound⟩ :=
    c28_flux_cutoff_kernel_global_euclidean_derivative_bound d D
  refine ⟨Cenv, Cder, henv, hder, ?_⟩
  intro Q i r hr s hs χ hχ hc R hsupp habs hgrad k dirs x z ψ W
  let g : Vec d → ℝ := fun y => Real.sqrt (∑ j : Fin d, ‖fderiv ℝ ψ y (unitVector j)‖ ^ 2)
  let K : Set (Vec d) := {y | euclideanNorm (y - z) ≤ R * r}
  let A : ℝ := Real.sqrt (d : ℝ) * (Cder k * (R / r) * s ^ (-(k : ℝ) / 2) +
    Cder (k + 1) * s ^ (-((k + 1 : ℕ) : ℝ) / 2)) * W
  have hregular := c28_flux_cutoff_kernel_tsupport Q i r s hr hs χ hχ hc hsupp k dirs x z
  have hK : IsCompact K := isCompact_physical_euclidean_closedBall z (R * r)
  have hψsub : tsupport ψ ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro v hv
    apply hsupp
    simp only [Function.mem_support] at hv ⊢
    intro hz
    apply hv
    simp [ψ, hz]
  have hzero (y : Vec d) (hy : y ∉ K) : g y = 0 := by
    have hd : fderiv ℝ ψ y = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hy (hψsub (tsupport_fderiv_subset ℝ h)))
    simp [g, hd]
  have hgcont : Continuous g := by
    dsimp [g]
    apply Real.continuous_sqrt.comp
    apply continuous_finsetSum
    intro j hj
    exact (((hregular.1.continuous_fderiv (by simp)).clm_apply continuous_const).norm).pow 2
  have hgcompact : HasCompactSupport g := by
    apply HasCompactSupport.of_support_subset_isCompact hK
    intro y hy
    by_contra hnot
    exact (Function.mem_support.mp hy) (hzero y hnot)
  have hint : Integrable g volume := hgcont.integrable_of_hasCompactSupport hgcompact
  refine ⟨hint, ?_⟩
  have hfinite : volume K ≠ ⊤ := ne_of_lt hK.measure_lt_top
  have hcomp : Integrable (K.indicator (fun _ : Vec d => A)) volume :=
    (integrableOn_const hfinite).integrable_indicator hK.measurableSet
  calc
    _ ≤ ∫ y, K.indicator (fun _ : Vec d => A) y ∂volume := by
      apply integral_mono_ae hint hcomp
      filter_upwards with y
      by_cases hy : y ∈ K
      · simpa [Set.indicator_of_mem hy, A, g] using
          (hbound Q i r hr s hs χ hχ hc hsupp habs hgrad k dirs x z y).2
      · simp [Set.indicator_of_notMem hy, hzero y hy, g]
    _ = _ := by rw [integral_indicator_const A hK.measurableSet]; simp [K, A, smul_eq_mul, Measure.real_def]


theorem c28_flux_gaussian_support_ball_volume
    (d : ℕ) : ∃ Cv : ℝ, 1 ≤ Cv ∧
    ∀ (r : ℝ), 1 ≤ r → ∀ z : Vec d,
      (volume {y : Vec d | euclideanNorm (y - z) ≤
        (2 * Real.sqrt (d : ℝ) + 2) * r}).toReal ≤ Cv * r ^ d := by
  let R : ℝ := 2 * Real.sqrt (d : ℝ) + 2
  have hR : 0 ≤ R := by dsimp [R]; positivity
  refine ⟨max 1 ((2 * R) ^ d), le_max_left _ _, ?_⟩
  intro r hr z
  have hr0 : 0 ≤ r := by linarith
  let a : Vec d := fun i => z i - R * r
  let b : Vec d := fun i => z i + R * r
  have hab : a ≤ b := by
    intro i
    dsimp [a, b]
    nlinarith [mul_nonneg hR hr0]
  have hsub : {y : Vec d | euclideanNorm (y - z) ≤ R * r} ⊆ Set.Icc a b := by
    intro y hy
    constructor <;> intro i
    all_goals
      have h := (EinsteinFull.Calculus.S1.abs_apply_le_euclideanNorm (y - z) i).trans hy
      simp only [Pi.sub_apply, abs_le] at h
      dsimp [a, b]
      linarith [h.1, h.2]
  have hfinite : volume (Set.Icc a b) ≠ ⊤ := ne_of_lt (isCompact_Icc.measure_lt_top)
  calc
    _ ≤ (volume (Set.Icc a b)).toReal := ENNReal.toReal_mono hfinite (measure_mono hsub)
    _ = (2 * R * r) ^ d := by
      rw [Real.volume_Icc_pi_toReal hab]
      have heq : (fun i : Fin d => b i - a i) = fun _ => 2 * R * r := by
        funext i
        dsimp [a, b]
        ring
      rw [heq]
      simp
    _ = (2 * R) ^ d * r ^ d := by rw [mul_pow]
    _ ≤ max 1 ((2 * R) ^ d) * r ^ d :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hr0 _)

theorem c28_flux_selected_good_ball_volume
    (d : ℕ) (A : ℝ) (hA : 1 ≤ A) :
    ∃ Cv : ℝ, 1 ≤ Cv ∧ ∀ r : ℝ, 1 ≤ r → ∀ z : Vec d,
      (volume {y : Vec d | euclideanNorm (y - z) <
        A * (((2 * Real.sqrt (d : ℝ) + 2) + 1) * r)}).toReal ≤
          Cv * r ^ d := by
  let R : ℝ := 2 * Real.sqrt (d : ℝ) + 2
  let B : ℝ := A * (R + 1)
  have hR : 1 ≤ R := by dsimp [R]; have := Real.sqrt_nonneg (d : ℝ); linarith
  have hB : 1 ≤ B := by dsimp [B]; nlinarith
  obtain ⟨C, hC, hvol⟩ := c28_flux_gaussian_support_ball_volume d
  refine ⟨C * B ^ d, ?_, ?_⟩
  · have hpow : 1 ≤ B ^ d := one_le_pow₀ hB
    nlinarith
  · intro r hr z
    have ht : 1 ≤ B * r := by nlinarith
    have hsub : {y : Vec d | euclideanNorm (y - z) < A * ((R + 1) * r)} ⊆
        {y : Vec d | euclideanNorm (y - z) ≤ R * (B * r)} := by
      intro y hy
      have hbr : 0 ≤ B * r := by positivity
      have hle : B * r ≤ R * (B * r) := by nlinarith
      change euclideanNorm (y - z) < A * ((R + 1) * r) at hy
      have heq : A * ((R + 1) * r) = B * r := by dsimp [B]; ring
      rw [heq] at hy
      exact hy.le.trans hle
    have hfinite : volume {y : Vec d | euclideanNorm (y - z) ≤ R * (B * r)} ≠ ⊤ := by
      let a : Vec d := fun i => z i - R * (B * r)
      let b : Vec d := fun i => z i + R * (B * r)
      have hcube : {y : Vec d | euclideanNorm (y - z) ≤ R * (B * r)} ⊆ Set.Icc a b := by
        intro y hy
        constructor <;> intro i
        all_goals
          have h := (EinsteinFull.Calculus.S1.abs_apply_le_euclideanNorm (y - z) i).trans hy
          simp only [Pi.sub_apply, abs_le] at h
          dsimp [a, b]
          linarith [h.1, h.2]
      exact ne_of_lt (lt_of_le_of_lt (measure_mono hcube) isCompact_Icc.measure_lt_top)
    calc
      _ ≤ (volume {y : Vec d | euclideanNorm (y - z) ≤ R * (B * r)}).toReal :=
        ENNReal.toReal_mono hfinite (measure_mono hsub)
      _ ≤ C * (B * r) ^ d := hvol (B * r) ht z
      _ = (C * B ^ d) * r ^ d := by rw [mul_pow]; ring

end EinsteinFull.Blueprint
