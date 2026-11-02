import EinsteinFull.External.Source.GMPDirichletSpectralKernel

open MeasureTheory Filter EinsteinRelation EinsteinFull.External.Source.GMP
open scoped Topology ENNReal

namespace EinsteinFull.Calculus

/-- The prescribed-point initial trace of the actual weighted spectral row,
for continuous compactly supported tests. -/
def br14WeightedRowInitialTrace {d : ℕ} {ρ : Vec d → ℝ}
    {α : Vec d → Mat d} {R : ℝ} (s : DirichletSpectralResolution ρ α R) : Prop :=
  ∀ y ∈ sourceBall (0 : Vec d) R, ∀ ψ : Vec d → ℝ,
    Continuous ψ → HasCompactSupport ψ → tsupport ψ ⊆ sourceBall (0 : Vec d) R →
    Tendsto (fun t : ℝ => ∫ x, (∑' n, Real.exp (-s.eigenvalue n * t) *
      s.eigenfunction n y * s.eigenfunction n x) * ψ x ∂dirichletVolume ρ R)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (ψ y))

/-- Continuous positive density converts the weighted row initial trace into
 the native Lebesgue-kernel column initial trace at every prescribed pole. -/
theorem br14_native_column_initial_delta {d : ℕ} {κ R : ℝ}
    (hκ : 0 < κ) {ρ : Vec d → ℝ} {α : Vec d → Mat d}
    (hell : IsUniformlyElliptic κ ρ α) (hρ : Continuous ρ)
    (s : DirichletSpectralResolution ρ α R)
    (hrow : br14WeightedRowInitialTrace s)
    (y : Vec d) (hy : y ∈ sourceBall (0 : Vec d) R)
    (φ : Vec d → ℝ) (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ sourceBall (0 : Vec d) R) :
    Tendsto (fun t : ℝ => ∫ x in sourceBall (0 : Vec d) R,
      (ρ y * ∑' n, Real.exp (-s.eigenvalue n * t) *
        s.eigenfunction n x * s.eigenfunction n y) * φ x)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (φ y)) := by
  have hpos (x : Vec d) : 0 < ρ x := hκ.trans_le (hell.2.2 x).1
  let ψ : Vec d → ℝ := fun x => φ x / ρ x
  have hψ : Continuous ψ := hφ.div hρ (fun x => ne_of_gt (hpos x))
  have hψc : HasCompactSupport ψ := by
    change HasCompactSupport (φ * fun x => (ρ x)⁻¹)
    exact hc.mul_right
  have hψs : tsupport ψ ⊆ sourceBall (0 : Vec d) R := by
    apply Set.Subset.trans _ hs
    simpa only [ψ, div_eq_mul_inv, Pi.mul_apply, Pi.inv_apply] using
      (tsupport_mul_subset_left (f := φ) (g := fun x => (ρ x)⁻¹))
  have hv : ρ y * ψ y = φ y := by
    dsimp only [ψ]
    field_simp [ne_of_gt (hpos y)]
  have hlim := (hrow y hy ψ hψ hψc hψs).const_mul (ρ y)
  rw [hv] at hlim
  apply hlim.congr'
  filter_upwards [] with t
  rw [← integral_const_mul]
  change (∫ x, ρ y * ((∑' n, Real.exp (-s.eigenvalue n * t) *
    s.eigenfunction n y * s.eigenfunction n x) * ψ x)
    ∂(volume.restrict (sourceBall (0 : Vec d) R)).withDensity
      (fun x => ENNReal.ofReal (ρ x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul hell.1.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [ENNReal.toReal_ofReal (hpos x).le, smul_eq_mul]
  have hswap : (∑' n, Real.exp (-s.eigenvalue n * t) *
      s.eigenfunction n x * s.eigenfunction n y) =
      ∑' n, Real.exp (-s.eigenvalue n * t) *
        s.eigenfunction n y * s.eigenfunction n x :=
    tsum_congr (fun _ => by ring)
  rw [hswap]
  dsimp only [ψ]
  generalize (∑' n, Real.exp (-s.eigenvalue n * t) *
    s.eigenfunction n y * s.eigenfunction n x) = S
  field_simp [ne_of_gt (hpos x)]
  <;> ring

#print axioms br14_native_column_initial_delta

end EinsteinFull.Calculus
