import EinsteinFull.Calculus.C16TubeCutoffQuantitativeTrace

open MeasureTheory Filter
open scoped NNReal ENNReal Topology InnerProductSpace

namespace EinsteinFull.Calculus

open EinsteinRelation External.Source.GMP Blueprint.TubeProbability
open Blueprint.TubeProbability.DimensionLift

noncomputable section

/-- The supplied modes have representatives in the native Dirichlet space
and satisfy their variational equations against every native test. -/
theorem br06_native_spectral_eigenvectors {d : ℕ} {κ R : ℝ}
    (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α R) :
    ∃ u : ℕ → DirichletHilbertSpace (d := d) R hR,
      (∀ n, (s.square_integrable n).toLp (s.eigenfunction n) =
        dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1) (u n)) ∧
      ∀ n w, (∫ x in sourceBall (0 : Vec d) R,
        dot ((α x).mulVec (fun i => (u n).val (some i) x))
          (fun i => w.val (some i) x)) = s.eigenvalue n * inner ℝ
        (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1) (u n))
        (dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1) w) := by
  classical
  choose u hu hv using fun n =>
    c16_supplied_eigenfunction_dirichletEquation_all_dimensions hκ hR hell s n
  refine ⟨u, ?_, hv⟩
  intro n
  apply Lp.ext
  exact ((s.square_integrable n).coeFn_toLp).trans (hu n).symm

/-- The native shifted resolvent acts diagonally on the supplied spectrum. -/
theorem br06_native_spectral_compact_resolvent {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α R) :
    ∃ T : Lp ℝ 2 (dirichletVolume ρ R) →L[ℝ] Lp ℝ 2 (dirichletVolume ρ R),
      IsCompactOperator T ∧ ∀ n,
        T ((s.square_integrable n).toLp (s.eigenfunction n)) =
          (1 + s.eigenvalue n)⁻¹ • (s.square_integrable n).toLp (s.eigenfunction n) := by
  let J := dirichletHilbertInclusion ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1)
  let e : ℕ → Lp ℝ 2 (dirichletVolume ρ R) :=
    fun n => (s.square_integrable n).toLp (s.eigenfunction n)
  obtain ⟨u, hu, hv⟩ := br06_native_spectral_eigenvectors hκ hR hell s
  obtain ⟨S, hcompact, hvar⟩ :=
    exists_compact_dirichletHilbert_shifted_resolvent hd hκ hell R hR (show (0 : ℝ) < 1 by norm_num)
  refine ⟨J.comp S, hcompact, ?_⟩
  intro n
  have hsolve : u n = S ((1 + s.eigenvalue n) • e n) := by
    apply (hvar _ _).mpr
    intro w
    have hm : Integrable (fun x => ρ x * (u n).val none x * w.val none x)
        (volume.restrict (sourceBall (0 : Vec d) R)) := by
      simpa using dirichletHilbert_scaled_form_integrable hκ hell R hR 0 (u n) w
    have hg : Integrable (fun x => dot ((α x).mulVec (fun i => (u n).val (some i) x))
        (fun i => w.val (some i) x)) (volume.restrict (sourceBall (0 : Vec d) R)) := by
      have hi := (dirichletHilbert_scaled_form_integrable hκ hell R hR 1 (u n) w).sub hm
      apply hi.congr
      exact ae_of_all _ fun x => by dsimp; ring
    have hmass : (∫ x in sourceBall (0 : Vec d) R,
        ρ x * (u n).val none x * w.val none x) = inner ℝ (J (u n)) (J w) := by
      exact (dirichletVolume_inner_eq_native hκ hell R (J (u n)) (J w)
        (fun x => (u n).val none x) (fun x => w.val none x)
        (dirichletHilbertInclusion_coe ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1) (u n))
        (dirichletHilbertInclusion_coe ρ R hR κ⁻¹ (fun x _ => (hell.2.2 x).2.1) w)).symm
    simp only [one_mul]
    rw [integral_add hm hg, hmass, hv n w, ← hu n]
    simp only [real_inner_smul_left]
    ring
  have hscale : (1 + s.eigenvalue n) • (J (S (e n))) = e n := by
    calc
      _ = J (S ((1 + s.eigenvalue n) • e n)) := by simp only [map_smul]
      _ = J (u n) := by rw [← hsolve]
      _ = e n := (hu n).symm
  have hne : 1 + s.eigenvalue n ≠ 0 :=
    ne_of_gt (add_pos zero_lt_one (s.eigenvalue_pos n))
  change J (S (e n)) = (1 + s.eigenvalue n)⁻¹ • e n
  calc
    _ = (1 + s.eigenvalue n)⁻¹ • ((1 + s.eigenvalue n) • J (S (e n))) := by
      simp only [smul_smul, inv_mul_cancel₀ hne, one_smul]
    _ = _ := by rw [hscale]

/-- A compact operator has vanishing diagonal coefficients along every
orthonormal sequence. -/
theorem br06_compact_orthonormal_diagonal_tendsto_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : H →L[ℝ] H) (hT : IsCompactOperator T)
    (e : ℕ → H) (he : Orthonormal ℝ e) :
    Tendsto (fun n => inner ℝ (e n) (T (e n))) atTop (𝓝 0) := by
  obtain ⟨K, hK, hsub⟩ := hT.image_closedBall_subset_compact 1
  have hKmem (n : ℕ) : T (e n) ∈ K := by
    apply hsub
    refine ⟨e n, ?_, rfl⟩
    simp only [Metric.mem_closedBall, dist_zero_right, he.norm_eq_one n, le_refl]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨F, hF, hcover⟩ := Metric.totallyBounded_iff.mp hK.totallyBounded
    (ε / 2) (half_pos hε)
  have hcent : ∀ᶠ n in atTop, ∀ y ∈ F, ‖inner ℝ (e n) y‖ < ε / 2 := by
    apply (eventually_all_finite hF).2
    intro y hy
    have hsq : Tendsto (fun n => ‖inner ℝ (e n) y‖ ^ 2) atTop (𝓝 0) :=
      (he.inner_products_summable y).tendsto_atTop_zero
    have hs : ∀ᶠ n in atTop, ‖inner ℝ (e n) y‖ ^ 2 < (ε / 2) ^ 2 :=
      hsq.eventually (Iio_mem_nhds (sq_pos_of_pos (half_pos hε)))
    filter_upwards [hs] with n hn
    have hn0 := norm_nonneg (inner ℝ (e n) y)
    nlinarith
  filter_upwards [hcent] with n hn
  obtain ⟨y, hyF, hy⟩ : ∃ y ∈ F, T (e n) ∈ Metric.ball y (ε / 2) := by
    rcases Set.mem_iUnion.mp (hcover (hKmem n)) with ⟨y, hy⟩
    rcases Set.mem_iUnion.mp hy with ⟨hyF, hy⟩
    exact ⟨y, hyF, hy⟩
  have hdist : ‖T (e n) - y‖ < ε / 2 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hy
  have hcs : ‖inner ℝ (e n) (T (e n) - y)‖ ≤ ‖T (e n) - y‖ := by
    simpa only [he.norm_eq_one n, one_mul] using
      (norm_inner_le_norm (𝕜 := ℝ) (e n) (T (e n) - y))
  have ht := norm_add_le (inner ℝ (e n) (T (e n) - y)) (inner ℝ (e n) y)
  have heq : inner ℝ (e n) (T (e n) - y) + inner ℝ (e n) y =
      inner ℝ (e n) (T (e n)) := by rw [inner_sub_right, sub_add_cancel]
  rw [heq] at ht
  simpa only [dist_zero_right] using (show ‖inner ℝ (e n) (T (e n))‖ < ε by
    linarith [hn y hyF])

/-- Each bounded interval contains only finitely many indices of the supplied
spectrum, independently of the order of its enumeration. -/
theorem br06_native_spectral_bounded_eigenvalues_finite {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α R) (M : ℝ) :
    {n : ℕ | s.eigenvalue n ≤ M}.Finite := by
  obtain ⟨T, hT, hdiag⟩ := br06_native_spectral_compact_resolvent hd hκ hR hell s
  let e : ℕ → Lp ℝ 2 (dirichletVolume ρ R) :=
    fun n => (s.square_integrable n).toLp (s.eigenfunction n)
  have hcoeff : Tendsto (fun n => (1 + s.eigenvalue n)⁻¹) atTop (𝓝 0) := by
    convert br06_compact_orthonormal_diagonal_tendsto_zero T hT e s.orthonormal using 1
    funext n
    rw [hdiag n, inner_smul_right]
    change (1 + s.eigenvalue n)⁻¹ =
      (1 + s.eigenvalue n)⁻¹ * inner ℝ (e n) (e n)
    have he : Orthonormal ℝ e := s.orthonormal
    simp only [real_inner_self_eq_norm_sq, he.norm_eq_one n, one_pow, mul_one]
  have hevent : ∀ᶠ n in atTop, ¬ s.eigenvalue n ≤ M := by
    by_cases hM : M ≤ 0
    · exact Filter.Eventually.of_forall (fun n hn =>
        (not_lt_of_ge (le_trans hn hM)) (s.eigenvalue_pos n))
    · have hMp : 0 < 1 + M := by linarith
      have heps := (Metric.tendsto_nhds.mp hcoeff) ((1 + M)⁻¹) (inv_pos.mpr hMp)
      filter_upwards [heps] with n hn
      have hnpos : 0 < 1 + s.eigenvalue n :=
        add_pos zero_lt_one (s.eigenvalue_pos n)
      have hinv : (1 + s.eigenvalue n)⁻¹ < (1 + M)⁻¹ := by
        simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnpos)] using hn
      have h := (inv_lt_inv₀ hnpos hMp).mp hinv
      linarith
  have hcof : ∀ᶠ n in Filter.cofinite, ¬ s.eigenvalue n ≤ M := by
    simpa only [Nat.cofinite_eq_atTop] using hevent
  have hf := Filter.eventually_cofinite.mp hcof
  simpa only [not_not] using hf

/-- Every supplied native spectral resolution escapes to infinity, regardless
of the order in which its eigenfunctions are listed. -/
theorem br06_native_spectral_eigenvalue_tendsto_atTop {d : ℕ} (hd : 2 ≤ d)
    {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
    {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α R) :
    Tendsto s.eigenvalue atTop atTop := by
  apply tendsto_atTop.2
  intro M
  have hf := br06_native_spectral_bounded_eigenvalues_finite hd hκ hR hell s M
  have hevent : ∀ᶠ n in atTop, n ∉ {n : ℕ | s.eigenvalue n ≤ M} := by
    simpa only [Nat.cofinite_eq_atTop] using hf.eventually_cofinite_notMem
  filter_upwards [hevent] with n hn
  exact (lt_of_not_ge hn).le

#print axioms br06_native_spectral_eigenvectors
#print axioms br06_native_spectral_compact_resolvent
#print axioms br06_compact_orthonormal_diagonal_tendsto_zero
#print axioms br06_native_spectral_bounded_eigenvalues_finite
#print axioms br06_native_spectral_eigenvalue_tendsto_atTop

end
end EinsteinFull.Calculus
