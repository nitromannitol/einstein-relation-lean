import EinsteinRelation.External.GilbargTrudinger
/-! # Subtraction of regular corrector representatives

Source: `paper/main.tex:861–867`. The actual Fréchet gradients and the
full bounded Hölder controls subtract with one shared gradient bound.
-/

namespace EinsteinRelation.Correctors
open External.GilbargTrudinger

private theorem HolderBound.sub {d : ℕ} {U : Set (Vec d)} {α : ℝ} {f g : Vec d → ℝ} {Kf Kg : ℝ}
    (hf : HolderBound U α f Kf) (hg : HolderBound U α g Kg) :
    HolderBound U α (f - g) (Kf + Kg) := by
  obtain ⟨Sf, Hf, hSf, hHf, hKf, hsupf, hholdf⟩ := hf
  obtain ⟨Sg, Hg, hSg, hHg, hKg, hsupg, hholdg⟩ := hg
  refine ⟨Sf + Sg, Hf + Hg, by nlinarith, by nlinarith,
    by nlinarith, ?_, ?_⟩
  · intro x hx
    have h1 : |f x| ≤ Sf := hsupf x hx
    have h2 : |g x| ≤ Sg := hsupg x hx
    calc
      |(f - g) x| = |f x - g x| := by simp [Pi.sub_apply]
      _ ≤ |f x| + |g x| := abs_sub _ _
      _ ≤ Sf + Sg := by nlinarith
  · intro x hx y hy
    have hxy : (f - g) x - (f - g) y = (f x - f y) - (g x - g y) := by
      simp [Pi.sub_apply]
      ring
    rw [hxy]
    have h1 : |f x - f y| ≤ Hf * euclideanNorm (x - y) ^ α := hholdf x hx y hy
    have h2 : |g x - g y| ≤ Hg * euclideanNorm (x - y) ^ α := hholdg x hx y hy
    calc
      |(f x - f y) - (g x - g y)| ≤ |f x - f y| + |g x - g y| := abs_sub _ _
      _ ≤ (Hf * euclideanNorm (x - y) ^ α) + (Hg * euclideanNorm (x - y) ^ α) := by nlinarith
      _ = (Hf + Hg) * euclideanNorm (x - y) ^ α := by ring

/-- Regular paired corrector representatives can be subtracted;
paper/main.tex:861–867. -/
theorem C1Alpha.sub {d : ℕ} {U : Set (Vec d)} {α : ℝ}
    {u v : Vec d → ℝ} {G H : Vec d → Vec d}
    (hu : C1Alpha U α u G) (hv : C1Alpha U α v H) :
    C1Alpha U α (fun x => u x - v x) (fun x => G x - H x) := by
  obtain ⟨hu_deriv, hu_K, hu_bound⟩ := hu
  obtain ⟨hv_deriv, hv_K, hv_bound⟩ := hv
  refine ⟨fun x hx => ?_, hu_K + hv_K, fun i => ?_⟩
  · have hu_fd := hu_deriv x hx
    have hv_fd := hv_deriv x hx
    have hsub := hu_fd.sub hv_fd
    have hderiv : (∑ i : Fin d, (G x i) • (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ)) -
        (∑ i : Fin d, (H x i) • (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ)) =
        ∑ i : Fin d, ((G - H) x i) • (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ) := by
      calc
        (∑ i : Fin d, (G x i) • (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ)) -
            (∑ i : Fin d, (H x i) • (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ)) =
            ∑ i : Fin d, ((G x i) • (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ) -
              (H x i) • (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ)) := by
          rw [Finset.sum_sub_distrib]
        _ = ∑ i : Fin d, ((G x i - H x i) • (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simpa using (sub_smul (G x i) (H x i) (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ)).symm
        _ = ∑ i : Fin d, ((G - H) x i) • (ContinuousLinearMap.proj i : Vec d →L[ℝ] ℝ) := by
          simp [Pi.sub_apply]
    simpa [hderiv] using hsub
  · have hGi := hu_bound i
    have hHi := hv_bound i
    exact HolderBound.sub hGi hHi
end EinsteinRelation.Correctors
