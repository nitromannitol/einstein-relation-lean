import EinsteinFull.Homogenization.SourceResponseStationarity
import EinsteinRelation.Clock.HeatCubeDecomposition

/-!
# Coloring response energies

Triadic cubes of the same nonnegative scale can be colored by their residues
modulo three. The local response energies of each color are jointly independent
under the finite-range hypothesis of Armstrong, Kuusi and Mourrat, *Quantitative
Stochastic Homogenization and Large-Scale Regularity*, Chapter 1.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.Clock

/-- Same-scale triadic cubes with the same residue color are separated by
at least twice their side length. -/
theorem cubeSet_dist_of_same_colour {d n : ℕ} {Q R : TriadicCube d}
    (hQ : Q.scale = n) (hR : R.scale = n) (hne : Q.index ≠ R.index)
    (hcol : heatCubeColour 3 Q.index = heatCubeColour 3 R.index)
    {x y : Vec d} (hx : x ∈ cubeSet Q) (hy : y ∈ cubeSet R) :
    2 * (3 : ℝ) ^ n ≤ EinsteinRelation.euclideanNorm (x - y) := by
  let L : ℝ := (3 : ℝ) ^ n
  have hL : 0 < L := by dsimp [L]; positivity
  have hfactorQ : cubeScaleFactor Q = L := by simp [cubeScaleFactor, hQ, L, zpow_natCast]
  have hfactorR : cubeScaleFactor R = L := by simp [cubeScaleFactor, hR, L, zpow_natCast]
  have hx' : (fun i => x i + L / 2) ∈ heatCube L Q.index := by
    intro i
    have hi := hx i
    rw [hfactorQ] at hi
    constructor <;> dsimp <;> nlinarith [hi.1, hi.2]
  have hy' : (fun i => y i + L / 2) ∈ heatCube L R.index := by
    intro i
    have hi := hy i
    rw [hfactorR] at hi
    constructor <;> dsimp <;> nlinarith [hi.1, hi.2]
  have h := heatCube_dist_of_same_colour hL 3 hne hcol _ hx' _ hy'
  have heq : (fun i => x i + L / 2) - (fun i => y i + L / 2) = x - y := by
    ext i
    simp only [Pi.sub_apply]
    ring
  rw [heq] at h
  simpa only [Nat.cast_ofNat, show (3 : ℝ) - 1 = 2 by norm_num, L] using h

/-- At each nonnegative scale, each residue class of distinct triadic cubes
has jointly independent response energies. -/
theorem iIndepFun_sourceResponseJ_colour {ι : Type*} [Fintype ι]
    {d : ℕ} [NeZero d] {K : ℝ} (P : Measure (Coefficient d K))
    [IsProbabilityMeasure P] (hP : AKMFiniteRange P)
    (Q : ι → TriadicCube d) (n : ℕ) (hscale : ∀ i, (Q i).scale = n)
    (hinj : Function.Injective fun i => (Q i).index)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : ι → Vec d)
    (c : Fin d → ZMod 3) :
    ProbabilityTheory.iIndepFun (fun i : {i : ι // heatCubeColour 3 (Q i).index = c} =>
      fun a => Book.Ch02.responseJ (Book.Ch02.cubeDomain (Q i))
        (sourceCoeffOn a (Book.Ch02.cubeDomain (Q i)) k hk) (p i) (q i)) P := by
  classical
  apply iIndepFun_sourceResponseJ_of_separated P hP 2 (by norm_num)
    (fun i : {i : ι // heatCubeColour 3 (Q i).index = c} => Q i) ?_ k hk
    (fun i => p i) (fun i => q i)
  intro i j hij x hx y hy
  have hne : (Q i).index ≠ (Q j).index := by
    intro h
    exact hij (Subtype.ext (hinj h))
  have h := cubeSet_dist_of_same_colour (hscale i) (hscale j) hne
    (i.property.trans j.property.symm) hx hy
  have hpow : (1 : ℝ) ≤ (3 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  linarith

end EinsteinFull.Homogenization
