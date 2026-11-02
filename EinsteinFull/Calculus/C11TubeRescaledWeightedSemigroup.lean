import EinsteinFull.Calculus.C16TubeCutoffQuantitativeTrace
import EllipticRegularity.Parabolic.Rescale.AffineMeasure

open EinsteinRelation MeasureTheory EinsteinFull.External.Source.GMP

noncomputable section
namespace EinsteinFull.Calculus

/-- The inner product of two supplied spectral heat rows gives the spectral
kernel at the sum of their times, in every finite dimension. -/
theorem c11_supplied_heat_row_inner {d : ℕ}
    {ρ : Vec d → ℝ} {α : Vec d → Mat d} {R : ℝ}
    (s : DirichletSpectralResolution ρ α R)
    (hspec : ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
      ∀ y ∈ sourceBall (0 : Vec d) R,
        Summable (fun n => Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y))
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (x y : Vec d) (hx : x ∈ sourceBall 0 R) (hy : y ∈ sourceBall 0 R) :
    inner ℝ (∑' i, (Real.exp (-s.eigenvalue i * p) * s.eigenfunction i x) •
      (s.square_integrable i).toLp (s.eigenfunction i))
      (∑' i, (Real.exp (-s.eigenvalue i * q) * s.eigenfunction i y) •
      (s.square_integrable i).toLp (s.eigenfunction i)) =
    ∑' i, Real.exp (-s.eigenvalue i * (p + q)) *
      s.eigenfunction i x * s.eigenfunction i y := by
  let row : Lp ℝ 2 (dirichletVolume ρ R) := ∑' i,
    (Real.exp (-s.eigenvalue i * q) * s.eigenfunction i y) •
      (s.square_integrable i).toLp (s.eigenfunction i)
  have ha := c16_supplied_heat_row_action_coordinates s hspec p hp x hx row
  have he : inner ℝ (∑' i, (Real.exp (-s.eigenvalue i * p) * s.eigenfunction i x) •
      (s.square_integrable i).toLp (s.eigenfunction i)) row =
      ∫ z, (∑' i, Real.exp (-s.eigenvalue i * p) *
        s.eigenfunction i x * s.eigenfunction i z) * row z ∂dirichletVolume ρ R := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [c16_supplied_heat_row_Lp_ae_eq s hspec p hp x hx] with z hz
    simp only [RCLike.inner_apply, conj_trivial]
    rw [hz]
    ring
  rw [he, ha]
  apply tsum_congr
  intro i
  rw [c16_supplied_heat_row_basis_coordinate s hspec q hq y hy]
  calc
    _ = (Real.exp (-s.eigenvalue i * p) * Real.exp (-s.eigenvalue i * q)) *
        s.eigenfunction i x * s.eigenfunction i y := by ring
    _ = _ := by
      rw [← Real.exp_add]
      congr 2
      ring


/-- The supplied spectral rows multiply to an integrable weighted kernel,
with the composition identity at every pair of interior points. -/
theorem c11_supplied_spectral_row_composition {d : ℕ}
    {κ R : ℝ} (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α)
    (s : DirichletSpectralResolution ρ α R)
    (hspec : ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
      ∀ y ∈ sourceBall (0 : Vec d) R,
        Summable (fun n => Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y))
    (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (x y : Vec d) (hx : x ∈ sourceBall 0 R) (hy : y ∈ sourceBall 0 R) :
    let k := fun t x z => ∑' i, Real.exp (-s.eigenvalue i * t) *
      s.eigenfunction i x * s.eigenfunction i z
    IntegrableOn (fun z => k p x z * k q y z * ρ z) (sourceBall 0 R) ∧
    k (p + q) x y = ∫ z in sourceBall 0 R, k p x z * k q y z * ρ z := by
  let k : ℝ → Vec d → Vec d → ℝ := fun t x z => ∑' i,
    Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x * s.eigenfunction i z
  let row : ℝ → Vec d → Lp ℝ 2 (dirichletVolume ρ R) := fun t x => ∑' i,
    (Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x) •
      (s.square_integrable i).toLp (s.eigenfunction i)
  have hae (t : ℝ) (ht : 0 < t) (x : Vec d) (hx : x ∈ sourceBall 0 R) :
      (fun z => row t x z) =ᵐ[dirichletVolume ρ R] k t x :=
    c16_supplied_heat_row_Lp_ae_eq s hspec t ht x hx
  have hk (t : ℝ) (ht : 0 < t) (x : Vec d) (hx : x ∈ sourceBall 0 R) :
      MemLp (k t x) 2 (dirichletVolume ρ R) :=
    (memLp_congr_ae (hae t ht x hx)).mp (Lp.memLp (row t x))
  have hint : Integrable (fun z => k p x z * k q y z) (dirichletVolume ρ R) :=
    (hk p hp x hx).integrable_mul (hk q hq y hy)
  have hρ0 : ∀ z, 0 ≤ ρ z := fun z => le_trans hκ.le (hell.2.2 z).1
  have hweight : IntegrableOn (fun z => k p x z * k q y z * ρ z) (sourceBall 0 R) := by
    unfold dirichletVolume at hint
    have hi := (integrable_withDensity_iff_integrable_smul' hell.1.ennreal_ofReal
      (ae_of_all _ fun z => ENNReal.ofReal_lt_top)).1 hint
    change Integrable (fun z => k p x z * k q y z * ρ z) (volume.restrict (sourceBall 0 R))
    simpa [hρ0, smul_eq_mul, mul_comm] using hi
  have hconvert : (∫ z, k p x z * k q y z ∂dirichletVolume ρ R) =
      ∫ z in sourceBall 0 R, k p x z * k q y z * ρ z := by
    unfold dirichletVolume
    rw [integral_withDensity_eq_integral_toReal_smul hell.1.ennreal_ofReal
      (ae_of_all _ fun z => ENNReal.ofReal_lt_top)]
    simp [hρ0, smul_eq_mul, mul_comm]
  have hinner : inner ℝ (row p x) (row q y) =
      ∫ z, k p x z * k q y z ∂dirichletVolume ρ R := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hae p hp x hx, hae q hq y hy] with z hz hz'
    simp only [RCLike.inner_apply, conj_trivial]
    rw [hz, hz']
    ring
  refine ⟨hweight, ?_⟩
  rw [← hconvert, ← hinner]
  exact (c11_supplied_heat_row_inner s hspec p q hp hq x y hx hy).symm


/-- The actual Lebesgue-density spectral kernel obeys weighted composition. -/
theorem c11_native_weighted_semigroup {d : ℕ} {κ R : ℝ} (hκ : 0 < κ)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
    (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
    (hK : IsSpectralDirichletFundamentalSolution ρ α R K G) :
    ∀ p q : ℝ, 0 < p → 0 < q → ∀ x ∈ sourceBall 0 R, ∀ y ∈ sourceBall 0 R,
      IntegrableOn (fun z => (K p x z / ρ z) * (K q z y / ρ y) * ρ z)
        (sourceBall 0 R) ∧
      K (p + q) x y / ρ y = ∫ z in sourceBall 0 R,
        (K p x z / ρ z) * (K q z y / ρ y) * ρ z := by
  obtain ⟨s, hs⟩ := hK.2
  have hspec : ∀ t : ℝ, 0 < t → ∀ x ∈ sourceBall (0 : Vec d) R,
      ∀ y ∈ sourceBall (0 : Vec d) R,
        Summable (fun n => Real.exp (-s.eigenvalue n * t) *
          s.eigenfunction n x * s.eigenfunction n y) :=
    fun t ht x hx y hy => (hs t ht x hx y hy).1
  let k : ℝ → Vec d → Vec d → ℝ := fun t x y => ∑' i,
    Real.exp (-s.eigenvalue i * t) * s.eigenfunction i x * s.eigenfunction i y
  have hk (t : ℝ) (ht : 0 < t) (x : Vec d) (hx : x ∈ sourceBall 0 R)
      (y : Vec d) (hy : y ∈ sourceBall 0 R) : K t x y / ρ y = k t x y := by
    rw [(hs t ht x hx y hy).2]
    exact mul_div_cancel_left₀ _ (ne_of_gt (lt_of_lt_of_le hκ (hell.2.2 y).1))
  have hsym (t : ℝ) (x y : Vec d) : k t x y = k t y x := by
    apply tsum_congr
    intro i
    ring
  intro p q hp hq x hx y hy
  have hrow := c11_supplied_spectral_row_composition hκ hell s hspec p q hp hq x y hx hy
  change IntegrableOn (fun z => k p x z * k q y z * ρ z) (sourceBall 0 R) ∧
    k (p + q) x y = ∫ z in sourceBall 0 R, k p x z * k q y z * ρ z at hrow
  have hball : MeasurableSet (sourceBall (0 : Vec d) R) :=
    (EinsteinFull.Blueprint.TubeProbability.dirichletBall (d := d) R).isOpen.measurableSet
  have hae : ∀ᵐ z ∂volume.restrict (sourceBall (0 : Vec d) R),
      (K p x z / ρ z) * (K q z y / ρ y) * ρ z = k p x z * k q y z * ρ z := by
    filter_upwards [ae_restrict_mem hball] with z hz
    rw [hk p hp x hx z hz, hk q hq z hz y hy, hsym q z y]
  have hae' : (fun z => (K p x z / ρ z) * (K q z y / ρ y) * ρ z) =ᵐ[volume.restrict (sourceBall 0 R)]
      (fun z => k p x z * k q y z * ρ z) := hae
  constructor
  · exact hrow.1.congr hae'.symm
  · rw [hk (p + q) (add_pos hp hq) x hx y hy, hrow.2]
    exact integral_congr_ae hae'.symm

private theorem c11_scale_embedding {d : ℕ} {r : ℝ} (hr : 0 < r) :
    MeasurableEmbedding (fun x : Vec d => r • x) :=
  (Homeomorph.smulOfNeZero r hr.ne').measurableEmbedding

private theorem c11_scale_map_volume {d : ℕ} {r : ℝ} (hr : 0 < r) :
    Measure.map (fun x : Vec d => r • x) volume =
      ENNReal.ofReal (|r ^ Module.finrank ℝ (Vec d)|⁻¹) • (volume : Measure (Vec d)) := by
  rw [Measure.map_addHaar_smul volume hr.ne', abs_inv]

/-- Rescaling transfers weighted composition on the whole corresponding ball. -/
theorem c11_rescaled_weighted_semigroup_of_composition {d : ℕ} (lam R : ℝ)
    (hlam : 0 < lam) (ρ : Vec d → ℝ) (K : ℝ → Vec d → Vec d → ℝ)
    (hComposition : ∀ s t : ℝ, 0 < s → 0 < t →
      ∀ x ∈ sourceBall 0 R, ∀ y ∈ sourceBall 0 R,
      IntegrableOn (fun z => (K s x z / ρ z) * (K t z y / ρ y) * ρ z)
        (sourceBall 0 R) ∧
      K (s+t) x y / ρ y = ∫ z in sourceBall 0 R,
        (K s x z / ρ z) * (K t z y / ρ y) * ρ z) :
    let S := lam * R
    let w : Vec d → ℝ := fun z => ρ (lam⁻¹ • z)
    let q : ℝ → Vec d → Vec d → ℝ := fun t x y =>
      (lam⁻¹)^d * K (t / lam^2) (lam⁻¹ • x) (lam⁻¹ • y) / ρ (lam⁻¹ • y)
    ∀ s t : ℝ, 0 < s → 0 < t → ∀ x ∈ sourceBall 0 S, ∀ y ∈ sourceBall 0 S,
      IntegrableOn (fun z => q s x z * q t z y * w z) (sourceBall 0 S) ∧
      q (s+t) x y = ∫ z in sourceBall 0 S, q s x z * q t z y * w z := by
  let T : Vec d → Vec d := fun z => lam⁻¹ • z
  have hemb : MeasurableEmbedding T := by
    exact c11_scale_embedding (inv_pos.mpr hlam)
  have hpre : T ⁻¹' sourceBall (0 : Vec d) R = sourceBall 0 (lam * R) := by
    ext z
    simp only [T, sourceBall, Set.mem_preimage, Set.mem_ofPred_eq, sub_zero,
      TimeChange.euclideanNorm_smul, abs_of_pos (inv_pos.mpr hlam)]
    rw [inv_mul_lt_iff₀ hlam]
  have hmap : Measure.map T (volume.restrict (sourceBall 0 (lam * R))) =
      ENNReal.ofReal (lam ^ d) • (volume : Measure (Vec d)).restrict (sourceBall 0 R) := by
    have hmset : MeasurableSet (sourceBall (0 : Vec d) R) :=
      (EinsteinFull.Blueprint.TubeProbability.dirichletBall (d := d) R).isOpen.measurableSet
    rw [← hpre, ← Measure.restrict_map hemb.measurable hmset]
    have hm := c11_scale_map_volume (d := d) (inv_pos.mpr hlam)
    simpa [T, Module.finrank_fin_fun, abs_of_pos (pow_pos (inv_pos.mpr hlam) _),
      inv_pow, abs_of_pos hlam, ENNReal.ofReal_pow] using congrArg (fun μ : Measure (Vec d) => μ.restrict (sourceBall 0 R)) hm
  dsimp only
  intro s t hs ht x hx y hy
  have hx' : T x ∈ sourceBall 0 R := by
    change x ∈ T ⁻¹' sourceBall 0 R
    rw [hpre]; exact hx
  have hy' : T y ∈ sourceBall 0 R := by
    change y ∈ T ⁻¹' sourceBall 0 R
    rw [hpre]; exact hy
  let p := s / lam^2
  let q := t / lam^2
  have hp : 0 < p := div_pos hs (pow_pos hlam _)
  have hq : 0 < q := div_pos ht (pow_pos hlam _)
  let f : Vec d → ℝ := fun z => (K p (T x) z / ρ z) * (K q z (T y) / ρ (T y)) * ρ z
  have hc := hComposition p q hp hq (T x) hx' (T y) hy'
  have hi : Integrable (f ∘ T) (volume.restrict (sourceBall 0 (lam * R))) :=
    PDE.Parabolic.Rescale.integrable_comp_of_map_eq_smul hemb ENNReal.ofReal_ne_top hmap hc.1
  have hint : (∫ z in sourceBall 0 (lam * R), f (T z)) =
      lam^d * ∫ z in sourceBall 0 R, f z := by
    simpa [ENNReal.toReal_ofReal (le_of_lt (pow_pos hlam _)), smul_eq_mul] using
      PDE.Parabolic.Rescale.integral_comp_of_map_eq_smul hemb hmap f
  have hcancel : (lam⁻¹)^d * lam^d = 1 := by
    rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hlam.ne')]
  constructor
  · change Integrable (fun z => ((lam⁻¹)^d * K p (T x) (T z) / ρ (T z)) *
        ((lam⁻¹)^d * K q (T z) (T y) / ρ (T y)) * ρ (T z)) _
    convert hi.const_mul ((lam⁻¹)^d * (lam⁻¹)^d) using 1 <;> ext z <;>
      simp only [f, Function.comp_apply]; ring
  · change (lam⁻¹)^d * K ((s+t)/lam^2) (T x) (T y) / ρ (T y) = _
    rw [mul_div_assoc, add_div]
    change (lam⁻¹)^d * (K (p+q) (T x) (T y) / ρ (T y)) = _
    rw [hc.2]
    calc
      (lam⁻¹)^d * (∫ z in sourceBall 0 R, f z) =
          ((lam⁻¹)^d * (lam⁻¹)^d) * (∫ z in sourceBall 0 (lam * R), f (T z)) := by
            rw [hint]
            rw [show (lam⁻¹)^d * (lam⁻¹)^d *
              (lam^d * ∫ z in sourceBall 0 R, f z) =
              (lam⁻¹)^d * ((lam⁻¹)^d * lam^d) *
                (∫ z in sourceBall 0 R, f z) by ring, hcancel, mul_one]
      _ = _ := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [] with z
        simp only [f]
        ring

/-- The actual spectral kernel has its weighted semigroup after spatial rescaling. -/
theorem c11_rescaled_weighted_semigroup {d : ℕ} (lam R κ : ℝ)
 (hlam : 0 < lam) (hR : 0 < R) (hκ : 0 < κ)
 (ρ : Vec d → ℝ) (α : Vec d → Mat d) (hell : IsUniformlyElliptic κ ρ α)
 (K : ℝ → Vec d → Vec d → ℝ) (G : ℝ → Vec d → Vec d → Vec d)
 (hK : IsSpectralDirichletFundamentalSolution ρ α R K G) :
 let S := lam * R
 let w : Vec d → ℝ := fun z => ρ (lam⁻¹ • z)
 let q : ℝ → Vec d → Vec d → ℝ := fun t x y =>
   (lam⁻¹)^d * K (t / lam^2) (lam⁻¹ • x) (lam⁻¹ • y) / ρ (lam⁻¹ • y)
 ∀ s t : ℝ, 0 < s → 0 < t → ∀ x ∈ sourceBall 0 S, ∀ y ∈ sourceBall 0 S,
 IntegrableOn (fun z => q s x z * q t z y * w z) (sourceBall 0 S) ∧
 q (s+t) x y = ∫ z in sourceBall 0 S, q s x z * q t z y * w z := by
  by_cases h : 0 < R
  · exact c11_rescaled_weighted_semigroup_of_composition lam R hlam ρ K
      (c11_native_weighted_semigroup hκ ρ α hell K G hK)
  · exact (h hR).elim

end EinsteinFull.Calculus
