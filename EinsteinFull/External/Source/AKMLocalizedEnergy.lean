import EinsteinFull.External.Source.AKMCoarsenedObjects
import EinsteinRelation.External.AKMLocalCorrectors

/-! # AKM's finite-domain localization of J₁

These are the literal optimization objects of AKM, Section 4.4,
printed pp.155–156 and (4.103), p.162. The construction is parameterized by
the structural constants used there. Existence of minimizing selectors,
their local measurability, and their quantitative approximation properties
are separate obligations; none is a field of an arbitrary random energy.
-/

open MeasureTheory

noncomputable section
namespace EinsteinFull.External.Source.AKM
open EinsteinRelation EinsteinRelation.External.AKM
open EinsteinRelation.Environment.AKMTestIntegralSupport

/-- The exponent ε immediately following AKM (4.85). -/
def localizationEpsilon (δ α γ : ℝ) : ℝ :=
  min ((α * (1 + δ) + δ - γ) / (1 + α)) (δ / 2)

/-- The containing radius T=r^(1+δ), AKM p.155. -/
def localizationOuterRadius (δ r : ℝ) : ℝ := r ^ (1 + δ)

/-- The intermediate radius S=r^(1+δ−ε), AKM p.155. -/
def localizationIntermediateRadius (δ α γ r : ℝ) : ℝ :=
  r ^ (1 + δ - localizationEpsilon δ α γ)

/-- The integer m in (4.86). Valid source parameters make its argument
positive. The ceiling is only data; no regularity theorem is presumed. -/
def localizationRegularityOrder (d : ℕ) (δ α γ : ℝ) : ℕ :=
  ⌈(d : ℝ) * (1 + δ) / localizationEpsilon δ α γ⌉₊

/-- Actual finite-domain H¹ weak a-harmonic functions A(B_T(z)). Values
outside the domain are immaterial to every functional below. In particular,
these functions need not be whole-space subquadratic harmonic functions. -/
structure LocalHarmonic {d : ℕ} {K : ℝ} (a : Coefficient d K)
    (z : Vec d) (T : ℝ) where
  /-- Potential on the source ball. -/
  potential : Vec d → ℝ
  /-- Its actual weak Euclidean gradient on that ball. -/
  grad : Vec d → Vec d
  square_integrable : MemLp potential 2 (volume.restrict (ball z T))
  gradient_square_integrable :
    MemLp (fun x => euclideanNorm (grad x)) 2 (volume.restrict (ball z T))
  weak_gradient : HasWeakGradient (ball z T) potential grad
  harmonic :
    HasWeakDivergence (ball z T) (fun x => (a x).mulVec (grad x)) (fun _ => 0)

/-- The admissible convex class K on p.155: the normalized gradient L²
norm is at most C. The constant is a structural choice in source theorems. -/
def IsLocalizationAdmissible {d : ℕ} {K : ℝ} {a : Coefficient d K}
    {z : Vec d} {T : ℝ} (C : ℝ) (w : LocalHarmonic a z T) : Prop :=
  vectorRms volume (ball z T) w.grad ≤ C

/-- The objective I on p.155. The OUTER integral is a volume average;
the inner Gaussian convolution is not renormalized after truncation. -/
def localizationObjective {d : ℕ} (z : Vec d) (T S σ θ : ℝ)
    (w : Vec d → ℝ) : ℝ :=
  ⨍ y in ball z (S / θ), (∫ x in ball z T, heatKernel y (σ * S) x * w x) ^ 2

/-- The literal coordinate minimization on p.155. Coordinates are taken
relative to the center, translating the source's ℓ_{e_i}(x)=x_i at z=0. -/
def IsCoordinateMinimizer {d : ℕ} {K : ℝ} {a : Coefficient d K}
    {z : Vec d} {T : ℝ} (S σ θ C : ℝ) (i : Fin d)
    (w : LocalHarmonic a z T) : Prop :=
  IsLocalizationAdmissible C w ∧
    ∀ v : LocalHarmonic a z T, IsLocalizationAdmissible C v →
      localizationObjective z T S σ θ (fun x => w.potential x - (x - z) i) ≤
        localizationObjective z T S σ θ (fun x => v.potential x - (x - z) i)

/-- The source's permissible tie-break on p.156: among actual minimizers,
choose a representative with smallest L²(B_T) norm. No existence is assumed. -/
def IsLeastNormCoordinateMinimizer {d : ℕ} {K : ℝ} {a : Coefficient d K}
    {z : Vec d} {T : ℝ} (S σ θ C : ℝ) (i : Fin d)
    (w : LocalHarmonic a z T) : Prop :=
  IsCoordinateMinimizer S σ θ C i w ∧
    ∀ v : LocalHarmonic a z T, IsCoordinateMinimizer S σ θ C i v →
      (∫ x in ball z T, w.potential x ^ 2) ≤
        ∫ x in ball z T, v.potential x ^ 2

/-- The d genuine selected coordinate minimizers defining V_r^δ on p.156.
This carrier records only the source minimization, without locality,
measurability, linear independence, estimates or a homogenized coefficient. -/
structure LocalizedBasis {d : ℕ} {K : ℝ} (a : Coefficient d K)
    (z : Vec d) (T S σ θ C : ℝ) where
  /-- The source coordinate potentials and their weak gradients. -/
  coordinate : Fin d → LocalHarmonic a z T
  /-- Exact variational selection, including the stated least-norm tie-break. -/
  selected : ∀ i, IsLeastNormCoordinateMinimizer S σ θ C i (coordinate i)

/-- An element of V_r^δ, expressed as a linear combination of the selected
coordinate potentials. Coefficients are arbitrary real numbers. -/
def localizedPotential {d : ℕ} {K : ℝ} {a : Coefficient d K}
    {z : Vec d} {T S σ θ C : ℝ}
    (W : LocalizedBasis a z T S σ θ C) (c : Vec d) (x : Vec d) : ℝ :=
  ∑ i, c i * (W.coordinate i).potential x

/-- The corresponding linear combination of the actual weak gradients. -/
def localizedGradient {d : ℕ} {K : ℝ} {a : Coefficient d K}
    {z : Vec d} {T S σ θ C : ℝ}
    (W : LocalizedBasis a z T S σ θ C) (c : Vec d) (x : Vec d) : Vec d :=
  ∑ i, c i • (W.coordinate i).grad x

/-- The truncated source Gaussian (4.89), translated to z. Its integral is
not adjusted to one. -/
def truncatedLocalizationKernel {d : ℕ} (z : Vec d) (r T : ℝ) : Vec d → ℝ :=
  Set.indicator (ball z T) (heatKernel z r)

/-- The energy in (4.103), now over the actual selected finite-dimensional
space. Its supremum is over every real linear combination of the d selected
potentials. It is not an affine-Dirichlet energy or a smoothed commutator. -/
def localizedEnergyJ1 {d : ℕ} {K : ℝ} {a : Coefficient d K}
    {z : Vec d} {T S σ θ C : ℝ}
    (W : LocalizedBasis a z T S σ θ C) (r : ℝ) (p q : Vec d) : ℝ :=
  sSup {e : ℝ | ∃ c : Vec d,
    e = ∫ x in ball z T, heatKernel z r x *
      (-(1 / 2 : ℝ) * dot (localizedGradient W c x)
          ((a x).mulVec (localizedGradient W c x)) -
        dot p ((a x).mulVec (localizedGradient W c x)) +
          dot q (localizedGradient W c x))}

/-- Polarization of this genuine localization with the same second load in
both terms, matching Definition5.23 before centering. -/
def localizedCoarsenedCoefficient {d : ℕ} {K : ℝ} {a : Coefficient d K}
    {z : Vec d} {T S σ θ C : ℝ}
    (W : LocalizedBasis a z T S σ θ C) (A : Mat d) (r : ℝ) : Mat d := fun j k =>
  (localizedEnergyJ1 W r (unitVector j + unitVector k) (A.mulVec (unitVector j)) -
    localizedEnergyJ1 W r (unitVector j - unitVector k) (A.mulVec (unitVector j))) / 2

/-- The source ε is positive under the strict exponent window (4.84). -/
theorem localizationEpsilon_pos {δ α γ : ℝ} (hδ : 0 < δ) (hα : 0 < α)
    (hγ : γ < α * (1 + δ) + δ) : 0 < localizationEpsilon δ α γ := by
  exact lt_min (div_pos (sub_pos.mpr hγ) (by linarith)) (by linarith)

/-- The source ε is at most δ/2. -/
theorem localizationEpsilon_le_half (δ α γ : ℝ) :
    localizationEpsilon δ α γ ≤ δ / 2 := min_le_right _ _

/-- Valid parameters give the strict intermediate scale r<S<T, as on p.155. -/
theorem localization_radius_order {δ α γ r : ℝ} (hδ : 0 < δ) (hα : 0 < α)
    (hγ : γ < α * (1 + δ) + δ) (hr : 1 < r) :
    r < localizationIntermediateRadius δ α γ r ∧
      localizationIntermediateRadius δ α γ r < localizationOuterRadius δ r := by
  have hε := localizationEpsilon_pos hδ hα hγ
  have hhalf := localizationEpsilon_le_half δ α γ
  constructor
  · simpa only [Real.rpow_one] using!
      Real.rpow_lt_rpow_of_exponent_lt hr (show (1 : ℝ) <
        1 + δ - localizationEpsilon δ α γ by linarith)
  · exact Real.rpow_lt_rpow_of_exponent_lt hr (by linarith)

/-- Truncation retains the ordinary Gaussian at every interior point. -/
theorem truncatedLocalizationKernel_of_mem {d : ℕ} {z : Vec d} {r T : ℝ}
    {x : Vec d} (hx : x ∈ ball z T) :
    truncatedLocalizationKernel z r T x = heatKernel z r x :=
  Set.indicator_of_mem hx _

/-- The source kernel is zero outside the containing ball. -/
theorem truncatedLocalizationKernel_of_notMem {d : ℕ} {z : Vec d} {r T : ℝ}
    {x : Vec d} (hx : x ∉ ball z T) :
    truncatedLocalizationKernel z r T x = 0 :=
  Set.indicator_of_notMem hx _

end EinsteinFull.External.Source.AKM
