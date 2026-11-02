import EinsteinFull.Calculus.CarverSFluxBlockGain
import EinsteinFull.Frozen.GaussianTestControl
import EinsteinFull.Calculus.C6GaussianOrderProductMajorant

open scoped BigOperators
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull

private theorem c10_lineDeriv_cast {V E : Type*} [LineDeriv V E E]
    {n m : ℕ} (h : n = m) (u : Fin m → V) (f : E) :
    LineDeriv.iteratedLineDerivOp (u ∘ Fin.cast h) f =
      LineDeriv.iteratedLineDerivOp u f := by
  subst m
  rfl

private theorem c10_lineDeriv_append {V E : Type*} [LineDeriv V E E]
    (q k : ℕ) (u : Fin q → V) (v : Fin k → V) (f : E) :
    LineDeriv.iteratedLineDerivOp (Fin.append u v) f =
      LineDeriv.iteratedLineDerivOp u (LineDeriv.iteratedLineDerivOp v f) := by
  induction q with
  | zero =>
    have hu : u = Fin.elim0 := Subsingleton.elim _ _
    subst u
    rw [Fin.elim0_append]
    exact c10_lineDeriv_cast (Nat.zero_add k) v f
  | succ q ih =>
    let h : (q + k) + 1 = (q + 1) + k := by omega
    let w : Fin ((q + k) + 1) → V := Fin.append u v ∘ Fin.cast h
    have hw : LineDeriv.iteratedLineDerivOp w f =
        LineDeriv.iteratedLineDerivOp (Fin.append u v) f :=
      c10_lineDeriv_cast h _ _
    have hw0 : w 0 = u 0 := by
      simp only [w, Function.comp_apply]
      rw [show Fin.cast h 0 = Fin.castAdd k (0 : Fin (q + 1)) from rfl, Fin.append_left]
    have hwtail : Fin.tail w = Fin.append (Fin.tail u) v := by
      ext j
      induction j using Fin.addCases with
      | left l =>
        simp only [w, Fin.tail, Function.comp_apply, Fin.append_left]
        rw [show Fin.cast h (Fin.castAdd k l).succ = Fin.castAdd k l.succ from rfl,
          Fin.append_left]
      | right r =>
        simp only [w, Fin.tail, Function.comp_apply, Fin.append_right]
        rw [show Fin.cast h (Fin.natAdd q r).succ = Fin.natAdd (q + 1) r from
          Fin.ext (by simp; omega),
          Fin.append_right]
    rw [← hw, LineDeriv.iteratedLineDerivOp_succ_left,
      LineDeriv.iteratedLineDerivOp_succ_left, hw0, hwtail, ih]

theorem c10_gaussian_derivative_normalized_test_control
    (d : ℕ) (D : StructuralData d) :
    ∃ c : ℝ, ∃ A B : ℕ → ℝ, 0 < c ∧ (∀ k, 0 < A k) ∧ (∀ q, 0 < B q) ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (i : Fin d)
      (s : ℝ) (hs : 0 < s) (k : ℕ) (dirs : Fin k → Fin d),
      HasGaussianTestControl s k c B
        (((A k : ℂ)⁻¹) • unforcedGaussianDerivativeSchwartz Q i s hs k dirs) := by
  obtain ⟨Cenv, Cder, henv, hder, hbound⟩ := carverS_flux_block_gaussian_envelope d D
  obtain ⟨A, B, hA, hB, hAB⟩ := c6_order_sum_positive_product_majorant Cder
  have henvpos : 0 < Cenv := lt_of_lt_of_le zero_lt_one henv
  refine ⟨Cenv⁻¹, A, B, inv_pos.mpr henvpos, hA, hB, ?_⟩
  intro Q i s hs k dirs q dirs' x
  have hlist : (fun j => unitVector (Fin.append dirs' dirs j)) =
      Fin.append (fun j => unitVector (dirs' j)) (fun j => unitVector (dirs j)) := by
    ext j
    induction j using Fin.addCases <;> simp
  have hb := hbound Q i s hs (q+k) (Fin.append dirs' dirs) x
  have hp : s ^ (-((q+k : ℕ) : ℝ) / 2) * s ^ (-(d : ℝ) / 2) =
      s ^ (-(d : ℝ) / 2 - ((q+k : ℕ) : ℝ) / 2) := by
    rw [← Real.rpow_add hs]
    congr 1
    ring
  have he : -euclideanNorm x ^ 2 / (Cenv * s) =
      -Cenv⁻¹ * euclideanNorm x ^ 2 / s := by simp only [div_eq_mul_inv, mul_inv_rev]; ring
  have hb' : ‖iteratedFDeriv ℝ (q+k) (homogenizedGaussianKernel Q i s hs 0) x
      (fun j => unitVector (Fin.append dirs' dirs j))‖ ≤
      Cder (q+k) * (s ^ (-(d : ℝ) / 2 - ((q+k : ℕ) : ℝ) / 2) *
        Real.exp (-Cenv⁻¹ * euclideanNorm x ^ 2 / s)) := by
    rw [he] at hb
    calc
      _ ≤ Cder (q+k) * s ^ (-((q+k : ℕ) : ℝ) / 2) *
          (s ^ (-(d : ℝ) / 2) * Real.exp (-Cenv⁻¹ * euclideanNorm x ^ 2 / s)) := hb
      _ = _ := by rw [← hp]; ring
  have hscalar : Cder (q+k) / A k ≤ B q := by
    apply (div_le_iff₀ (hA k)).2
    have h := (le_max_right 1 (Cder (k+q))).trans (hAB k q)
    simpa [Nat.add_comm, mul_comm] using h
  have hnonneg : 0 ≤ s ^ (-(d : ℝ) / 2 - ((q+k : ℕ) : ℝ) / 2) *
      Real.exp (-Cenv⁻¹ * euclideanNorm x ^ 2 / s) := by positivity
  change ‖iteratedFDeriv ℝ q (fun y =>
    (((A k : ℂ)⁻¹) • unforcedGaussianDerivativeSchwartz Q i s hs k dirs) y) x
      (fun j => unitVector (dirs' j))‖ ≤ _
  rw [← SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv,
    LineDeriv.iteratedLineDerivOp_smul]
  simp only [smul_apply, norm_smul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (hA k)]
  rw [unforcedGaussianDerivativeSchwartz, ← c10_lineDeriv_append, hlist.symm,
    SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
  have hfun : (unforcedGaussianSchwartz Q i s hs : Vec d → ℂ) =
      homogenizedGaussianKernel Q i s hs 0 := funext (unforcedGaussianSchwartz_apply Q i s hs)
  rw [hfun]
  calc
    _ ≤ (A k)⁻¹ * (Cder (q+k) * (s ^ (-(d : ℝ) / 2 - ((q+k : ℕ) : ℝ) / 2) *
        Real.exp (-Cenv⁻¹ * euclideanNorm x ^ 2 / s))) :=
      mul_le_mul_of_nonneg_left hb' (le_of_lt (inv_pos.mpr (hA k)))
    _ ≤ _ := by
      convert mul_le_mul_of_nonneg_right hscalar hnonneg using 1 <;> ring

end EinsteinFull.Blueprint
