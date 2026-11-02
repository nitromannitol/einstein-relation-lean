import EinsteinFull.Calculus.C12TubeFixedTimeLowerAssembly
import EinsteinFull.Calculus.SbxBCappedTubeChainR02

open EinsteinRelation MeasureTheory EinsteinFull.External.Source.GMP
open PDE hiding Vec Mat

namespace EinsteinFull.Calculus

/-- A positive one-step bound on a concentric interior ball propagates over
any finite number of steps in the same weighted semigroup. -/
theorem b_capped_weighted_interior_chain {d : ℕ}
    (S τ κ a : ℝ) (hS : 0 < S) (hτ : 0 < τ) (hκ : 0 < κ) (ha : 0 < a)
    (N : ℕ) (hN : 0 < N) (ρ : Vec d → ℝ) (q : ℝ → Vec d → Vec d → ℝ)
    (hρ : ∀ z, κ ≤ ρ z) (hq : ∀ s, 0 < s → ∀ x y, 0 ≤ q s x y)
    (hint : ∀ s t, 0 < s → 0 < t → ∀ x ∈ sourceBall 0 S, ∀ y ∈ sourceBall 0 S,
      IntegrableOn (fun z => q s x z * q t z y * ρ z) (sourceBall 0 S))
    (hsemi : ∀ s t, 0 < s → 0 < t → ∀ x ∈ sourceBall 0 S, ∀ y ∈ sourceBall 0 S,
      q (s+t) x y = ∫ z in sourceBall 0 S, q s x z * q t z y * ρ z)
    (hstep : ∀ x ∈ sourceBall 0 (S/2), ∀ y ∈ sourceBall 0 (S/2), a ≤ q τ x y) :
    ∀ x ∈ sourceBall 0 (S/2), ∀ y ∈ sourceBall 0 (S/2),
      a * (a * κ * (volume (sourceBall (0 : Vec d) (S/2))).toReal)^(N-1) ≤
        q ((N : ℝ) * τ) x y := by
  let U : Set (Vec d) := sourceBall 0 S
  let B : Set (Vec d) := sourceBall 0 (S/2)
  have hB : MeasurableSet B := (c12_sourceBall_volume (0 : Vec d) (by positivity : 0 < S/2)).1
  have hBU : B ⊆ U := by
    intro z hz
    change euclideanNorm (z-0) < S/2 at hz
    change euclideanNorm (z-0) < S
    linarith
  have hfin : volume U ≠ ⊤ := (c12_sourceBall_volume (0 : Vec d) hS).2.1
  haveI : IsFiniteMeasure (volume.restrict U) := isFiniteMeasure_restrict.mpr hfin
  let v : ℝ := (volume B).toReal
  have hv : 0 < v := (c12_sourceBall_volume (0 : Vec d) (by positivity : 0 < S/2)).2.2.1
  have hvol : ∀ k : ℕ, v ≤ ((volume.restrict U) B).toReal := by
    intro k
    rw [Measure.restrict_apply hB, Set.inter_eq_left.mpr hBU]
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  intro x hx y hy
  have hchain := c12_weighted_real_semigroup_finite_chain (volume.restrict U) ρ κ a v τ
    hκ.le ha.le hv.le hτ hρ q hq U (fun _ => B) (fun _ => hB) (fun _ => hBU)
    hvol (fun _ => hstep) hint hsemi x hx n y hy
  simpa [v, B, Nat.succ_eq_add_one] using hchain

open Classical in
/-- Arbitrary prescribed time has a strictly positive normalized spectral
kernel lower bound on a concentric interior ball. The native short-time mass
and comparison estimates are kept as separate assumptions. -/
theorem b_native_capped_fixed_time_lower
    (d : ℕ) (hd : 2 ≤ d) (κ δ H S t : ℝ)
    (hκ : 0 < κ) (hδ : 0 < δ) (hH : 0 < H) (hS : 0 < S) (ht : 0 < t) :
    ∃ cstar : ℝ, 0 < cstar ∧ ∀ (R lam : ℝ),
    0 < R → 0 < lam → S = lam * R →
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
    ∀ (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
    IsSpectralDirichletFundamentalSolution ρ α R K G →
    (∀ (x : Vec d) (r u : ℝ), 0 < r → sourceBall x (2*r) ⊆ sourceBall 0 R →
      0 < u → u ≤ δ*r^2 → (1/2 : ℝ) ≤ ∫ y in sourceBall 0 R, K u x y) →
    (∀ (x y : Vec d) (r u : ℝ), 0 < r → sourceBall x (2*r) ⊆ sourceBall 0 R →
      y ∈ sourceBall 0 R → 0 < u → u ≤ δ*r^2 → euclideanSq (x-y) ≤ u →
      K (2*u) x x / ρ x ≤ H * (K (4*u) x y / ρ y)) →
    ∀ x ∈ sourceBall 0 (S/2), ∀ y ∈ sourceBall 0 (S/2),
      cstar ≤ (lam⁻¹)^d * K (t / lam^2) (lam⁻¹ • x) (lam⁻¹ • y) / ρ (lam⁻¹ • y) := by
  obtain ⟨A, B, hA, hB, hgaussian⟩ :=
    c12_native_rescaled_gaussian_of_mass_comparison d hd κ δ H hκ hδ hH
  obtain ⟨N, hN, hτ, _, hcap, _⟩ :=
    b_exists_capped_native_substeps t 1 1 S 0 ht (by norm_num) (by norm_num) hS (by norm_num)
  let τ : ℝ := t / (N : ℝ)
  obtain ⟨a, ha, hauniform⟩ :=
    c12_uniform_gaussian_ball_lower (d := d) τ (S/2) A B 0 hτ (by positivity) hA hB (by norm_num)
  let v : ℝ := (volume (sourceBall (0 : Vec d) (S/2))).toReal
  have hv : 0 < v := (c12_sourceBall_volume (0 : Vec d) (by positivity : 0 < S/2)).2.2.1
  refine ⟨a * (a * κ * v)^(N-1), by positivity, ?_⟩
  intro R lam hR hlam hSR ρ α hell K G hK hmass hcompare x hx y hy
  let q : ℝ → Vec d → Vec d → ℝ := fun u x y =>
    if x ∈ sourceBall 0 S ∧ y ∈ sourceBall 0 S then
      (lam⁻¹)^d * K (u / lam^2) (lam⁻¹ • x) (lam⁻¹ • y) / ρ (lam⁻¹ • y) else 0
  let w : Vec d → ℝ := fun z => max κ (ρ (lam⁻¹ • z))
  have hsem := c12_normalized_semigroup_of_unclipped lam R κ ρ α K hell
    (c11_rescaled_weighted_semigroup lam R κ hlam hR hκ ρ α hell K G hK)
  rw [← hSR] at hsem
  have hq : ∀ u, 0 < u → ∀ x y, 0 ≤ q u x y := by
    intro u hu x y
    dsimp only [q]
    split_ifs with hxy
    · have hscaled (z : Vec d) (hz : z ∈ sourceBall 0 S) :
          lam⁻¹ • z ∈ sourceBall 0 R := by
        change euclideanNorm (lam⁻¹ • z - 0) < R
        simp only [sub_zero, TimeChange.euclideanNorm_smul, abs_of_pos (inv_pos.mpr hlam)]
        have hz' : euclideanNorm z < S := by simpa [sourceBall] using hz
        rw [hSR] at hz'
        exact (inv_mul_lt_iff₀ hlam).2 hz'
      exact div_nonneg (mul_nonneg (pow_nonneg (inv_nonneg.mpr hlam.le) _)
        ((hK.1 (lam⁻¹ • y) (hscaled y hxy.2)).2.1
          (u / lam^2) (div_pos hu (sq_pos_of_pos hlam)) (lam⁻¹ • x) (hscaled x hxy.1)))
        (hκ.le.trans (hell.2.2 (lam⁻¹ • y)).1)
    · exact le_rfl
  have hstep : ∀ x ∈ sourceBall 0 (S/2), ∀ y ∈ sourceBall 0 (S/2), a ≤ q τ x y := by
    apply hauniform (0 : Vec d) (0 : Vec d) (by simp [euclideanNorm, euclideanSq, dot]) q
    intro z hz z' hz'
    exact hgaussian R S τ lam hR hS hτ hlam hSR hcap ρ α hell K G hK hmass hcompare z hz z' hz'
  have hchain := b_capped_weighted_interior_chain S τ κ a hS hτ hκ ha N hN w q
    (fun z => le_max_left _ _) hq
    (fun s u hs hu z hz z' hz' => (hsem s u hs hu z hz z' hz').1)
    (fun s u hs hu z hz z' hz' => (hsem s u hs hu z hz z' hz').2)
    hstep x hx y hy
  have htime : (N : ℝ) * τ = t := by
    dsimp [τ]
    field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)]
  rw [htime] at hchain
  have hxS : x ∈ sourceBall 0 S := by
    change euclideanNorm (x-0) < S/2 at hx
    change euclideanNorm (x-0) < S
    linarith
  have hyS : y ∈ sourceBall 0 S := by
    change euclideanNorm (y-0) < S/2 at hy
    change euclideanNorm (y-0) < S
    linarith
  simpa [q, hxS, hyS, v] using hchain


/-- The unscaled native normalized kernel has the same arbitrary-time bound
on the closed concentric quarter-radius ball. -/
theorem b_unscaled_native_capped_fixed_time_lower
    (d : ℕ) (hd : 2 ≤ d) (κ δ H R t : ℝ)
    (hκ : 0 < κ) (hδ : 0 < δ) (hH : 0 < H) (hR : 0 < R) (ht : 0 < t) :
    ∃ cstar : ℝ, 0 < cstar ∧
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
    ∀ (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
    IsSpectralDirichletFundamentalSolution ρ α R K G →
    (∀ (x : Vec d) (r u : ℝ), 0 < r → sourceBall x (2*r) ⊆ sourceBall 0 R →
      0 < u → u ≤ δ*r^2 → (1/2 : ℝ) ≤ ∫ y in sourceBall 0 R, K u x y) →
    (∀ (x y : Vec d) (r u : ℝ), 0 < r → sourceBall x (2*r) ⊆ sourceBall 0 R →
      y ∈ sourceBall 0 R → 0 < u → u ≤ δ*r^2 → euclideanSq (x-y) ≤ u →
      K (2*u) x x / ρ x ≤ H * (K (4*u) x y / ρ y)) →
    ∀ x, euclideanNorm (x - 0) ≤ R/4 → ∀ y, euclideanNorm (y - 0) ≤ R/4 →
      cstar ≤ K t x y / ρ y := by
  obtain ⟨cstar, hcstar, hbound⟩ :=
    b_native_capped_fixed_time_lower d hd κ δ H R t hκ hδ hH hR ht
  refine ⟨cstar, hcstar, ?_⟩
  intro ρ α hell K G hK hmass hcompare x hx y hy
  have hx' : x ∈ sourceBall 0 (R/2) := by
    change euclideanNorm (x - 0) < R/2
    linarith
  have hy' : y ∈ sourceBall 0 (R/2) := by
    change euclideanNorm (y - 0) < R/2
    linarith
  have h := hbound R 1 hR (by norm_num) (by simp) ρ α hell K G hK hmass hcompare x hx' y hy'
  simpa using h


/-- Source-oriented form of the spectral estimate. The inherited spectral
carrier uses endpoint density; transposing its arguments gives the source
kernel, which is normalized by the density at the source. -/
theorem b_source_oriented_capped_fixed_time_lower
    (d : ℕ) (hd : 2 ≤ d) (κ δ H S t : ℝ)
    (hκ : 0 < κ) (hδ : 0 < δ) (hH : 0 < H) (hS : 0 < S) (ht : 0 < t) :
    ∃ cstar : ℝ, 0 < cstar ∧ ∀ (R scale : ℝ),
    0 < R → 0 < scale → S = scale * R →
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
    ∀ (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
    IsSpectralDirichletFundamentalSolution ρ α R K G →
    (∀ (x : Vec d) (r u : ℝ), 0 < r → sourceBall x (2*r) ⊆ sourceBall 0 R →
      0 < u → u ≤ δ*r^2 → (1/2 : ℝ) ≤ ∫ y in sourceBall 0 R, K u x y) →
    (∀ (x y : Vec d) (r u : ℝ), 0 < r → sourceBall x (2*r) ⊆ sourceBall 0 R →
      y ∈ sourceBall 0 R → 0 < u → u ≤ δ*r^2 → euclideanSq (x-y) ≤ u →
      K (2*u) x x / ρ x ≤ H * (K (4*u) x y / ρ y)) →
    ∀ x ∈ sourceBall 0 (S/2), ∀ y ∈ sourceBall 0 (S/2),
      cstar ≤ (scale⁻¹)^d * K (t / scale^2) (scale⁻¹ • y) (scale⁻¹ • x) /
        ρ (scale⁻¹ • x) := by
  obtain ⟨cstar, hcstar, hbound⟩ :=
    b_native_capped_fixed_time_lower d hd κ δ H S t hκ hδ hH hS ht
  refine ⟨cstar, hcstar, ?_⟩
  intro R scale hR hscale hSR ρ α hell K G hK hmass hcompare x hx y hy
  exact hbound R scale hR hscale hSR ρ α hell K G hK hmass hcompare y hy x hx


/-- The source-normalized bound transports through the signed spatial scale.
The coefficient fields and kernel are quantified after the uniform constant. -/
theorem b_signed_source_capped_fixed_time_lower
    (d : ℕ) (hd : 2 ≤ d) (κ δ H S t : ℝ)
    (hκ : 0 < κ) (hδ : 0 < δ) (hH : 0 < H) (hS : 0 < S) (ht : 0 < t) :
    ∃ cstar : ℝ, 0 < cstar ∧ ∀ (R lam : ℝ),
    0 < R → lam ≠ 0 → S = |lam| * R →
    ∀ (ρ : Vec d → ℝ) (α : Vec d → Mat d), IsUniformlyElliptic κ ρ α →
    ∀ (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d),
    IsSpectralDirichletFundamentalSolution ρ α R K G →
    (∀ (x : Vec d) (r u : ℝ), 0 < r → sourceBall x (2*r) ⊆ sourceBall 0 R →
      0 < u → u ≤ δ*r^2 → (1/2 : ℝ) ≤ ∫ y in sourceBall 0 R, K u x y) →
    (∀ (x y : Vec d) (r u : ℝ), 0 < r → sourceBall x (2*r) ⊆ sourceBall 0 R →
      y ∈ sourceBall 0 R → 0 < u → u ≤ δ*r^2 → euclideanSq (x-y) ≤ u →
      K (2*u) x x / ρ x ≤ H * (K (4*u) x y / ρ y)) →
    ∀ x ∈ sourceBall 0 (S/2), ∀ y ∈ sourceBall 0 (S/2),
      cstar ≤ (|lam|⁻¹)^d * K (t / lam^2) (lam⁻¹ • y) (lam⁻¹ • x) /
        ρ (lam⁻¹ • x) := by
  obtain ⟨cstar, hcstar, hbound⟩ :=
    b_source_oriented_capped_fixed_time_lower d hd κ δ H S t hκ hδ hH hS ht
  refine ⟨cstar, hcstar, ?_⟩
  intro R lam hR hlam hSR ρ α hell K G hK hmass hcompare x hx y hy
  by_cases hp : 0 < lam
  · have hsR : S = lam * R := by simpa only [abs_of_pos hp] using hSR
    simpa only [abs_of_pos hp] using
      hbound R lam hR hp hsR ρ α hell K G hK hmass hcompare x hx y hy
  · have hn : lam < 0 := lt_of_le_of_ne (le_of_not_gt hp) hlam
    have hsR : S = (-lam) * R := by simpa only [abs_of_neg hn] using hSR
    have hnorm (z : Vec d) : euclideanNorm (-z) = euclideanNorm z := by
      simpa using (TimeChange.euclideanNorm_smul (-1 : ℝ) z)
    have hxneg : -x ∈ sourceBall 0 (S/2) := by
      change euclideanNorm (-x - 0) < S/2
      have hx' : euclideanNorm (x - 0) < S/2 := hx
      simpa only [sub_zero, hnorm] using hx'
    have hyneg : -y ∈ sourceBall 0 (S/2) := by
      change euclideanNorm (-y - 0) < S/2
      have hy' : euclideanNorm (y - 0) < S/2 := hy
      simpa only [sub_zero, hnorm] using hy'
    have h := hbound R (-lam) hR (neg_pos.mpr hn) hsR ρ α hell K G hK
      hmass hcompare (-x) hxneg (-y) hyneg
    simpa only [abs_of_neg hn, inv_neg, neg_smul, smul_neg, neg_neg, neg_sq] using h


/-- Transposing the native endpoint-normalized kernel produces the same
spectral series with the density at the source. -/
theorem b_native_spectral_source_transpose {d : ℕ}
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} {R : ℝ}
    {K : ℝ → Vec d → Vec d → ℝ} {G : ℝ → Vec d → Vec d → Vec d}
    (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
    {t : ℝ} (ht : 0 < t) {x y : Vec d}
    (hx : x ∈ sourceBall 0 R) (hy : y ∈ sourceBall 0 R) :
    ∃ spectrum : DirichletSpectralResolution ρ α R,
      K t y x = ρ x * ∑' n, Real.exp (-spectrum.eigenvalue n * t) *
        spectrum.eigenfunction n x * spectrum.eigenfunction n y ∧
      K t x y = ρ y * ∑' n, Real.exp (-spectrum.eigenvalue n * t) *
        spectrum.eigenfunction n x * spectrum.eigenfunction n y := by
  obtain ⟨spectrum, hspec⟩ := hK.2
  refine ⟨spectrum, ?_, (hspec t ht x hx y hy).2⟩
  rw [(hspec t ht y hy x hx).2]
  congr 1
  apply tsum_congr
  intro n
  ring

/-- The source-normalized transpose and endpoint-normalized native kernel
have the same value at every positive time and pair of interior points. -/
theorem b_native_spectral_normalized_transpose {d : ℕ}
    {κ : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α) {R : ℝ}
    {K : ℝ → Vec d → Vec d → ℝ} {G : ℝ → Vec d → Vec d → Vec d}
    (hK : IsSpectralDirichletFundamentalSolution ρ α R K G)
    {t : ℝ} (ht : 0 < t) {x y : Vec d}
    (hx : x ∈ sourceBall 0 R) (hy : y ∈ sourceBall 0 R) :
    K t y x / ρ x = K t x y / ρ y := by
  have hρx : ρ x ≠ 0 := ne_of_gt (lt_of_lt_of_le hκ (hell.2.2 x).1)
  have hρy : ρ y ≠ 0 := ne_of_gt (lt_of_lt_of_le hκ (hell.2.2 y).1)
  apply (div_eq_div_iff hρx hρy).2
  calc
    K t y x * ρ y = ρ y * K t y x := mul_comm _ _
    _ = ρ x * K t x y := (hK.weighted_symmetry ht hx hy).symm
    _ = K t x y * ρ x := mul_comm _ _

end EinsteinFull.Calculus
