import EinsteinFull.Calculus.C18PhysicalValueSmoothing
import EinsteinFull.Calculus.U8FourierFirstMoment

open EinsteinRelation MeasureTheory LineDeriv ENNReal
open scoped ENNReal NNReal Topology SchwartzMap FourierTransform Laplacian

namespace EinsteinFull

/-- Pairing with the transported L² class is unchanged by the coordinate
change. This applies in particular to Schwartz test functions. -/
private theorem u8_physical_L2_euclidean_pairing_isolated {d : ℕ}
    (u : Lp ℂ 2 (volume : Measure (Vec d)))
    (φ : EuclideanSpace ℝ (Fin d) → ℂ) :
    let J : EuclideanSpace ℝ (Fin d) → Vec d := WithLp.ofLp
    let hJ : MeasurePreserving J volume volume := PiLp.volume_preserving_ofLp (Fin d)
    let v := Lp.compMeasurePreserving J hJ u
    (∫ y, φ y * v y) = ∫ x : Vec d, φ (WithLp.toLp 2 x) * u x := by
  let J : EuclideanSpace ℝ (Fin d) → Vec d := WithLp.ofLp
  let K := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  have hJ : MeasurePreserving J volume volume := PiLp.volume_preserving_ofLp (Fin d)
  have hK : MeasurePreserving K volume volume := PiLp.volume_preserving_toLp (Fin d)
  let v := Lp.compMeasurePreserving J hJ u
  have hv : (fun x : Vec d => v (K x)) =ᵐ[volume] u := by
    have h := hK.quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_compMeasurePreserving u hJ)
    filter_upwards [h] with x hx
    simpa [J, K, v, Function.comp_def] using hx
  change (∫ y, φ y * v y) = ∫ x : Vec d, φ (K x) * u x
  calc
    (∫ y, φ y * v y) = ∫ x : Vec d, φ (K x) * v (K x) :=
      (hK.integral_comp K.toHomeomorph.measurableEmbedding (fun y => φ y * v y)).symm
    _ = ∫ x : Vec d, φ (K x) * u x := by
      apply integral_congr_ae
      filter_upwards [hv] with x hx
      rw [hx]

/-- Physical distributional coordinate derivatives commute with transport to
Euclidean coordinates. -/
private theorem u8_physical_euclidean_tempered_derivative_isolated {d : ℕ}
    (f g : Lp ℂ 2 (volume : Measure (Vec d))) (j : Fin d)
    (h : ∂_{unitVector j} (f : 𝓢'(Vec d, ℂ)) = (g : 𝓢'(Vec d, ℂ))) :
    let J : EuclideanSpace ℝ (Fin d) → Vec d := WithLp.ofLp
    let hJ : MeasurePreserving J volume volume := PiLp.volume_preserving_ofLp (Fin d)
    ∂_{WithLp.toLp 2 (unitVector j)}
        (Lp.compMeasurePreserving J hJ f : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) =
      (Lp.compMeasurePreserving J hJ g : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) := by
  let J : EuclideanSpace ℝ (Fin d) → Vec d := WithLp.ofLp
  let hJ : MeasurePreserving J volume volume := PiLp.volume_preserving_ofLp (Fin d)
  let K := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  change ∂_{K (unitVector j)}
      (Lp.compMeasurePreserving J hJ f : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) =
    (Lp.compMeasurePreserving J hJ g : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ))
  ext1 ψ
  let ψ' := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ K ψ
  have he := congrArg (fun T : 𝓢'(Vec d, ℂ) => T ψ') h
  rw [TemperedDistribution.lineDerivOp_apply_apply, Lp.toTemperedDistribution_apply,
    Lp.toTemperedDistribution_apply] at he ⊢
  have hd : ∂_{unitVector j} ψ' =
      SchwartzMap.compCLMOfContinuousLinearEquiv ℂ K (∂_{K (unitVector j)} ψ) :=
    SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv ℂ (unitVector j) K ψ
  rw [hd] at he
  simp only [neg_apply, smul_eq_mul] at he ⊢
  have hf := u8_physical_L2_euclidean_pairing_isolated f
    (fun y => -((∂_{K (unitVector j)} ψ) y))
  have hg := u8_physical_L2_euclidean_pairing_isolated g ψ
  rw [hf, hg]
  simpa only [ψ', SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    K, PiLp.coe_symm_continuousLinearEquiv] using he

/-- Transport the entire physical weak derivative chain to Euclidean space. -/
private theorem u8_physical_euclidean_iterated_tempered_derivative_isolated {d N : ℕ}
    (F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (hF : ∀ p, p.length < N →
      IsPhysicalH1Graph volume (Or.inl rfl) (F p) (fun j => F (p ++ [j])))
    (path steps : List (Fin d)) (horder : path.length + steps.length ≤ N) :
    let J : EuclideanSpace ℝ (Fin d) → Vec d := WithLp.ofLp
    let hJ : MeasurePreserving J volume volume := PiLp.volume_preserving_ofLp (Fin d)
    steps.foldl (fun u j => ∂_{WithLp.toLp 2 (unitVector j)} u)
        (Lp.compMeasurePreserving J hJ (F path) : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) =
      (Lp.compMeasurePreserving J hJ (F (path ++ steps)) :
        𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) := by
  induction steps generalizing path with
  | nil => simp
  | cons j steps ih =>
      have hp : path.length < N := by simp only [List.length_cons] at horder; omega
      have hs : (path ++ [j]).length + steps.length ≤ N := by
        simp only [List.length_append, List.length_cons, List.length_nil] at horder ⊢
        omega
      simp only [List.foldl_cons,
        u8_physical_euclidean_tempered_derivative_isolated (F path) (F (path ++ [j])) j
          (c18_tempered_derivative_of_physical_H1Graph (hF path hp) j)]
      simpa only [List.append_assoc, List.singleton_append] using ih (path ++ [j]) hs

/-- A bounded Euclidean C¹ representative pulls back without increasing its
supremum norm. -/
private theorem u8_physical_bounded_C1_pullback_isolated {d : ℕ}
    (v : BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℂ)
    (g : Vec d → ℂ) (hv : ContDiff ℝ 1 v)
    (he : (v : EuclideanSpace ℝ (Fin d) → ℂ) =ᵐ[volume]
      (fun y => g (WithLp.ofLp y))) :
    ∃ f : BoundedContinuousFunction (Vec d) ℂ,
      ContDiff ℝ 1 f ∧ (f : Vec d → ℂ) =ᵐ[volume] g ∧ ‖f‖ ≤ ‖v‖ := by
  let K := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  let Kc : C(Vec d, EuclideanSpace ℝ (Fin d)) := ⟨K, K.continuous⟩
  let f := v.compContinuous Kc
  have hp := c18_euclidean_C1_representative_pullback v g hv he
  refine ⟨f, ?_, ?_, ?_⟩
  · simpa [f, Kc, K, PiLp.coe_symm_continuousLinearEquiv, Function.comp_def] using hp.1
  · simpa [f, Kc, K, PiLp.coe_symm_continuousLinearEquiv, Function.comp_def] using hp.2.1
  · exact BoundedContinuousFunction.norm_compContinuous_le v Kc


/-- An even derivative order lies below the available chain and exceeds
    the threshold needed for one integrable Fourier moment. -/
theorem u8_sobolev_even_order (d : ℕ) :
    ∃ k : ℕ, 2 * k ≤ d + 3 ∧ d + 2 < 4 * k := by
  refine ⟨(d + 3) / 2, ?_, ?_⟩ <;> omega

/-- The Euclidean Laplacian of a transported weak derivative is the sum
of the corresponding second coordinate derivatives. -/
theorem u8_physical_euclidean_laplacian {d N : ℕ}
    (F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (hF : ∀ p, p.length < N →
      IsPhysicalH1Graph volume (Or.inl rfl) (F p) (fun j => F (p ++ [j])))
    (p : List (Fin d)) (hp : p.length + 2 ≤ N) :
    let J : EuclideanSpace ℝ (Fin d) → Vec d := WithLp.ofLp
    let hJ : MeasurePreserving J volume volume := PiLp.volume_preserving_ofLp (Fin d)
    Δ (Lp.compMeasurePreserving J hJ (F p) : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) =
      ∑ j : Fin d, (Lp.compMeasurePreserving J hJ (F (p ++ [j, j])) :
        𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) := by
  let J : EuclideanSpace ℝ (Fin d) → Vec d := WithLp.ofLp
  let hJ : MeasurePreserving J volume volume := PiLp.volume_preserving_ofLp (Fin d)
  change Δ (Lp.compMeasurePreserving J hJ (F p) : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) =
    ∑ j : Fin d, (Lp.compMeasurePreserving J hJ (F (p ++ [j, j])) :
      𝓢'(EuclideanSpace ℝ (Fin d), ℂ))
  rw [TemperedDistribution.laplacian_eq_sum (EuclideanSpace.basisFun (Fin d) ℝ)]
  apply Finset.sum_congr rfl
  intro j hj
  have hb : (EuclideanSpace.basisFun (Fin d) ℝ) j =
      WithLp.toLp 2 (unitVector j) := by
    ext i
    simp [unitVector, Pi.single_apply]
  rw [hb]
  have hd := u8_physical_euclidean_iterated_tempered_derivative_isolated F hF p [j, j] (by simpa using hp)
  simpa only [List.foldl_cons, List.foldl_nil] using hd

/-- At even order two, the Bessel potential is the identity minus a
scaled Laplacian, with the Fourier convention used here. -/
theorem u8_euclidean_besselPotential_two {d : ℕ}
    (T : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) :
    TemperedDistribution.besselPotential (EuclideanSpace ℝ (Fin d)) ℂ 2 T =
      T - ((2 * Real.pi) ^ 2 : ℝ)⁻¹ • Δ T := by
  let g : EuclideanSpace ℝ (Fin d) → ℂ := fun x => (‖x‖ ^ 2 : ℝ)
  have hplus : TemperedDistribution.besselPotential (EuclideanSpace ℝ (Fin d)) ℂ 2 T =
      T + TemperedDistribution.fourierMultiplierCLM ℂ g T := by
    unfold TemperedDistribution.besselPotential
    have hg : (fun x : EuclideanSpace ℝ (Fin d) =>
        (((1 + ‖x‖ ^ 2) ^ ((2 : ℝ) / 2) : ℝ) : ℂ)) =
        (fun _ => (1 : ℂ)) + g := by
      ext x
      simp [g]
    rw [hg, TemperedDistribution.fourierMultiplierCLM_apply,
      TemperedDistribution.smulLeftCLM_add (by fun_prop) (by fun_prop)]
    simp [TemperedDistribution.fourierMultiplierCLM_apply]
  rw [hplus, TemperedDistribution.laplacian_eq_fourierMultiplierCLM]
  have hc : (2 * Real.pi) ^ 2 ≠ 0 := by positivity
  simp [g, smul_smul, hc]

/-- L² realization of an iterated even-order Bessel potential, expressed
using only the supplied coordinate derivative family. -/
noncomputable def u8EuclideanBesselChain {d : ℕ}
    (F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d))) :
    ℕ → List (Fin d) → Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))
  | 0, p => Lp.compMeasurePreserving WithLp.ofLp
      (PiLp.volume_preserving_ofLp (Fin d)) (F p)
  | k + 1, p => u8EuclideanBesselChain F k p -
      ((2 * Real.pi) ^ 2 : ℝ)⁻¹ • ∑ j : Fin d,
        u8EuclideanBesselChain F k (p ++ [j, j])

/-- The finite coordinate chain gives a uniform L² bound for the Bessel
realization, with a constant depending only on the dimension and order. -/
theorem u8EuclideanBesselChain_norm_le {d N : ℕ}
    (F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (R : ℝ) (hR : ∀ p, p.length ≤ N → ‖F p‖ ≤ R)
    (k : ℕ) (p : List (Fin d)) (hp : p.length + 2 * k ≤ N) :
    ‖u8EuclideanBesselChain F k p‖ ≤
      (1 + (d : ℝ) * ((2 * Real.pi) ^ 2 : ℝ)⁻¹) ^ k * R := by
  let c : ℝ := ((2 * Real.pi) ^ 2)⁻¹
  let A : ℝ := 1 + (d : ℝ) * c
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  change ‖u8EuclideanBesselChain F k p‖ ≤ A ^ k * R
  induction k generalizing p with
  | zero =>
      simp only [u8EuclideanBesselChain, pow_zero, one_mul,
        Lp.norm_compMeasurePreserving]
      apply hR
      omega
  | succ k ih =>
      have hp0 : p.length + 2 * k ≤ N := by omega
      have hpi (j : Fin d) : (p ++ [j, j]).length + 2 * k ≤ N := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      have hsum : ‖∑ j : Fin d, u8EuclideanBesselChain F k (p ++ [j, j])‖ ≤
          (d : ℝ) * (A ^ k * R) := by
        calc
          _ ≤ ∑ j : Fin d, ‖u8EuclideanBesselChain F k (p ++ [j, j])‖ :=
            norm_sum_le _ _
          _ ≤ ∑ _j : Fin d, A ^ k * R := by
            apply Finset.sum_le_sum
            intro j hj
            exact ih (p ++ [j, j]) (hpi j)
          _ = _ := by simp
      calc
        ‖u8EuclideanBesselChain F (k + 1) p‖ ≤
            ‖u8EuclideanBesselChain F k p‖ +
              c * ‖∑ j : Fin d, u8EuclideanBesselChain F k (p ++ [j, j])‖ := by
          simpa [u8EuclideanBesselChain, c, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg hc] using norm_sub_le (u8EuclideanBesselChain F k p)
              (c • ∑ j : Fin d, u8EuclideanBesselChain F k (p ++ [j, j]))
        _ ≤ A ^ k * R + c * ((d : ℝ) * (A ^ k * R)) := by
          exact add_le_add (ih p hp0) (mul_le_mul_of_nonneg_left hsum hc)
        _ = A ^ (k + 1) * R := by rw [pow_succ]; dsimp [A]; ring

/-- The finite L² chain represents the even-order Bessel potential of the
transported weak derivative. -/
theorem u8EuclideanBesselChain_represents {d N : ℕ}
    (F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
    (hF : ∀ p, p.length < N →
      IsPhysicalH1Graph volume (Or.inl rfl) (F p) (fun j => F (p ++ [j])))
    (k : ℕ) (p : List (Fin d)) (hp : p.length + 2 * k ≤ N) :
    let J : EuclideanSpace ℝ (Fin d) → Vec d := WithLp.ofLp
    let hJ : MeasurePreserving J volume volume := PiLp.volume_preserving_ofLp (Fin d)
    TemperedDistribution.besselPotential (EuclideanSpace ℝ (Fin d)) ℂ (2 * (k : ℝ))
      (Lp.compMeasurePreserving J hJ (F p) : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) =
      (u8EuclideanBesselChain F k p : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) := by
  let J : EuclideanSpace ℝ (Fin d) → Vec d := WithLp.ofLp
  let hJ : MeasurePreserving J volume volume := PiLp.volume_preserving_ofLp (Fin d)
  induction k generalizing p with
  | zero =>
      simp [u8EuclideanBesselChain]
  | succ k ih =>
      have hp0 : p.length + 2 * k ≤ N := by omega
      have hp2 : p.length + 2 ≤ N := by omega
      have hpi (j : Fin d) : (p ++ [j, j]).length + 2 * k ≤ N := by
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      change TemperedDistribution.besselPotential (EuclideanSpace ℝ (Fin d)) ℂ
          (2 * ((k + 1 : ℕ) : ℝ))
          (Lp.compMeasurePreserving J hJ (F p) : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) = _
      have hpower (T : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) :
          TemperedDistribution.besselPotential (EuclideanSpace ℝ (Fin d)) ℂ
              (2 * ((k + 1 : ℕ) : ℝ)) T =
            TemperedDistribution.besselPotential (EuclideanSpace ℝ (Fin d)) ℂ (2 * (k : ℝ))
              (TemperedDistribution.besselPotential (EuclideanSpace ℝ (Fin d)) ℂ 2 T) := by
        convert (TemperedDistribution.besselPotential_besselPotential_apply
          2 (2 * (k : ℝ)) T).symm using 1; push_cast; ring
      rw [hpower, u8_euclidean_besselPotential_two,
        u8_physical_euclidean_laplacian F hF p hp2]
      simp only [map_sub, ContinuousLinearMap.map_smul_of_tower, map_sum]
      rw [ih p hp0]
      have hsum :
          (∑ j : Fin d, TemperedDistribution.besselPotential (EuclideanSpace ℝ (Fin d)) ℂ
            (2 * (k : ℝ)) (Lp.compMeasurePreserving J hJ (F (p ++ [j, j])) :
              𝓢'(EuclideanSpace ℝ (Fin d), ℂ))) =
          ∑ j : Fin d, (u8EuclideanBesselChain F k (p ++ [j, j]) :
              𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) := by
        apply Finset.sum_congr rfl
        intro j hj
        exact ih (p ++ [j, j]) (hpi j)
      rw [hsum]
      change _ = ((u8EuclideanBesselChain F k p -
        ((2 * Real.pi) ^ 2 : ℝ)⁻¹ • ∑ j : Fin d,
          u8EuclideanBesselChain F k (p ++ [j, j]) :
        Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
          𝓢'(EuclideanSpace ℝ (Fin d), ℂ))
      conv_rhs =>
        rw [← Lp.toTemperedDistributionCLM_apply, map_sub,
          ContinuousLinearMap.map_smul_of_tower, map_sum]
      simp only [Lp.toTemperedDistributionCLM_apply]

/-- A uniformly bounded finite weak-derivative chain yields a bounded C¹
representative, with a constant depending only on the dimension. -/
theorem u8_physical_high_weak_derivatives_C1_representative
    (d : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
      (R : ℝ), 0 ≤ R →
      (∀ p, p.length < d + 3 →
        IsPhysicalH1Graph volume (Or.inl rfl) (F p) (fun j => F (p ++ [j]))) →
      (∀ p, p.length ≤ d + 3 → ‖F p‖ ≤ R) →
      ∃ f : BoundedContinuousFunction (Vec d) ℂ,
        ContDiff ℝ 1 f ∧ (f : Vec d → ℂ) =ᵐ[volume] (F []) ∧ ‖f‖ ≤ C * R := by
  obtain ⟨k, hk, hk'⟩ := u8_sobolev_even_order d
  have hs : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) <
      2 * (2 * (k : ℝ) - 1) := by
    have h : (d : ℝ) + 2 < 4 * (k : ℝ) := by exact_mod_cast hk'
    simp only [finrank_euclideanSpace_fin]
    linarith
  obtain ⟨K, hK, hfourier⟩ := u8_euclidean_fourier_L1_with_first_moment hs
  let B : ℝ := (1 + (d : ℝ) * ((2 * Real.pi) ^ 2 : ℝ)⁻¹) ^ k
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨(K + 1) * (B + 1), by positivity, ?_⟩
  intro F R hR hF hbound
  let J : EuclideanSpace ℝ (Fin d) → Vec d := WithLp.ofLp
  let hJ : MeasurePreserving J volume volume := PiLp.volume_preserving_ofLp (Fin d)
  let f0 := Lp.compMeasurePreserving J hJ (F [])
  let u := 𝓕 (u8EuclideanBesselChain F k [])
  have hpot : TemperedDistribution.besselPotential (EuclideanSpace ℝ (Fin d)) ℂ
      (2 * (k : ℝ)) (f0 : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) =
      (u8EuclideanBesselChain F k [] : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) := by
    exact u8EuclideanBesselChain_represents F hF k [] (by simpa using hk)
  have hu : TemperedDistribution.smulLeftCLM ℂ
      (fun x => ((1 + ‖x‖ ^ 2) ^ ((2 * (k : ℝ)) / 2) : ℝ))
      (𝓕 (f0 : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ))) = u := by
    rw [← TemperedDistribution.fourier_besselPotential_eq_smulLeftCLM_fourier_apply,
      hpot, Lp.fourier_toTemperedDistribution_eq]
  obtain ⟨v, hv, hvnorm, hmoment⟩ := hfourier (f0 : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) u hu
  have hvC1 := u8_euclidean_inverse_fourier_C1 v hmoment
  have hvae := u8_euclidean_inverse_fourier_ae f0 v hv
  have htransport : (f0 : EuclideanSpace ℝ (Fin d) → ℂ) =ᵐ[volume]
      fun x => F [] (J x) := Lp.coeFn_compMeasurePreserving (F []) hJ
  obtain ⟨f, hf, hfe, hfnorm⟩ := u8_physical_bounded_C1_pullback_isolated
    (Real.Lp.fourierTransformInv v) (F []) hvC1 (hvae.trans htransport)
  refine ⟨f, hf, hfe, ?_⟩
  have hunorm : ‖u‖ ≤ B * R := by
    dsimp [u, B]
    rw [Lp.norm_fourier_eq]
    exact u8EuclideanBesselChain_norm_le F R hbound k [] (by simpa using hk)
  have hfac : K * B ≤ (K + 1) * (B + 1) := by nlinarith
  calc
    ‖f‖ ≤ ‖Real.Lp.fourierTransformInv v‖ := hfnorm
    _ ≤ ‖v‖ := u8_euclidean_inverse_fourier_norm_le v
    _ ≤ K * ‖u‖ := hvnorm
    _ ≤ K * (B * R) := mul_le_mul_of_nonneg_left hunorm hK
    _ = (K * B) * R := by ring
    _ ≤ ((K + 1) * (B + 1)) * R := mul_le_mul_of_nonneg_right hfac hR


/-- A quantitative bound for the physical representative and its derivative. -/
theorem u8_physical_high_weak_derivatives_C1_quantitative
    (d : ℕ) : ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧
    ∀ (F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
      (R : ℝ), 0 ≤ R →
      (∀ p, p.length < d + 3 →
        IsPhysicalH1Graph volume (Or.inl rfl) (F p) (fun j => F (p ++ [j]))) →
      (∀ p, p.length ≤ d + 3 → ‖F p‖ ≤ R) →
      ∃ f : BoundedContinuousFunction (Vec d) ℂ,
        ContDiff ℝ 1 f ∧ (f : Vec d → ℂ) =ᵐ[volume] (F []) ∧
        ‖f‖ ≤ C * R ∧ ∀ x, ‖fderiv ℝ f x‖ ≤ D * R := by
  obtain ⟨k, hk, hk'⟩ := u8_sobolev_even_order d
  have hs : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) <
      2 * (2 * (k : ℝ) - 1) := by
    have h : (d : ℝ) + 2 < 4 * (k : ℝ) := by exact_mod_cast hk'
    simp only [finrank_euclideanSpace_fin]
    linarith
  obtain ⟨K, M, hK, hM, hfourier⟩ := u8_euclidean_fourier_L1_quantitative hs
  let B : ℝ := (1 + (d : ℝ) * ((2 * Real.pi) ^ 2 : ℝ)⁻¹) ^ k
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let E := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  refine ⟨(K + 1) * (B + 1), (2 * Real.pi * M) * B * ‖E.toContinuousLinearMap‖,
    by positivity, by positivity, ?_⟩
  intro F R hR hF hbound
  let J : EuclideanSpace ℝ (Fin d) → Vec d := WithLp.ofLp
  let hJ : MeasurePreserving J volume volume := PiLp.volume_preserving_ofLp (Fin d)
  let f0 := Lp.compMeasurePreserving J hJ (F [])
  let u := 𝓕 (u8EuclideanBesselChain F k [])
  have hpot : TemperedDistribution.besselPotential (EuclideanSpace ℝ (Fin d)) ℂ
      (2 * (k : ℝ)) (f0 : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) =
      (u8EuclideanBesselChain F k [] : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) := by
    exact u8EuclideanBesselChain_represents F hF k [] (by simpa using hk)
  have hu : TemperedDistribution.smulLeftCLM ℂ
      (fun x => ((1 + ‖x‖ ^ 2) ^ ((2 * (k : ℝ)) / 2) : ℝ))
      (𝓕 (f0 : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ))) = u := by
    rw [← TemperedDistribution.fourier_besselPotential_eq_smulLeftCLM_fourier_apply,
      hpot, Lp.fourier_toTemperedDistribution_eq]
  obtain ⟨v, hv, hvnorm, hmoment, hmoment_bound⟩ := hfourier (f0 : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) u hu
  have hvC1 := u8_euclidean_inverse_fourier_C1 v hmoment
  have hvae := u8_euclidean_inverse_fourier_ae f0 v hv
  have htransport : (f0 : EuclideanSpace ℝ (Fin d) → ℂ) =ᵐ[volume]
      fun x => F [] (J x) := Lp.coeFn_compMeasurePreserving (F []) hJ
  let Ec : C(Vec d, EuclideanSpace ℝ (Fin d)) := ⟨E, E.continuous⟩
  let f := (Real.Lp.fourierTransformInv v).compContinuous Ec
  have hp := c18_euclidean_C1_representative_pullback
    (Real.Lp.fourierTransformInv v) (F []) hvC1 (hvae.trans htransport)
  have hf : ContDiff ℝ 1 f := by
    simpa [f, Ec, E, PiLp.coe_symm_continuousLinearEquiv, Function.comp_def] using hp.1
  have hfe : (f : Vec d → ℂ) =ᵐ[volume] (F []) := by
    simpa [f, Ec, E, PiLp.coe_symm_continuousLinearEquiv, Function.comp_def] using hp.2.1
  have hfnorm : ‖f‖ ≤ ‖Real.Lp.fourierTransformInv v‖ :=
    BoundedContinuousFunction.norm_compContinuous_le _ _
  refine ⟨f, hf, hfe, ?_⟩
  have hunorm : ‖u‖ ≤ B * R := by
    dsimp [u, B]
    rw [Lp.norm_fourier_eq]
    exact u8EuclideanBesselChain_norm_le F R hbound k [] (by simpa using hk)
  have hfac : K * B ≤ (K + 1) * (B + 1) := by nlinarith
  constructor
  · calc
      ‖f‖ ≤ ‖Real.Lp.fourierTransformInv v‖ := hfnorm
      _ ≤ ‖v‖ := u8_euclidean_inverse_fourier_norm_le v
      _ ≤ K * ‖u‖ := hvnorm
      _ ≤ K * (B * R) := mul_le_mul_of_nonneg_left hunorm hK
      _ = (K * B) * R := by ring
      _ ≤ ((K + 1) * (B + 1)) * R := mul_le_mul_of_nonneg_right hfac hR
  · intro x
    have hcomp : (f : Vec d → ℂ) = (fun z => Real.Lp.fourierTransformInv v (E z)) := by
      rfl
    rw [hcomp]
    change ‖fderiv ℝ ((fun z => Real.Lp.fourierTransformInv v z) ∘ E) x‖ ≤ _
    rw [fderiv_comp x (hvC1.differentiable (by norm_num) _) E.differentiableAt]
    change ‖fderiv ℝ (fun z => Real.Lp.fourierTransformInv v z) (E x) ∘SL
      fderiv ℝ (fun z => E.toContinuousLinearMap z) x‖ ≤ _
    rw [E.toContinuousLinearMap.fderiv]
    calc
      _ ≤ ‖fderiv ℝ (fun z => Real.Lp.fourierTransformInv v z) (E x)‖ *
          ‖E.toContinuousLinearMap‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (2 * Real.pi * (M * ‖u‖)) * ‖E.toContinuousLinearMap‖ := by
        gcongr
        exact (u8_euclidean_inverse_fourier_derivative_bound v hmoment (E x)).trans
          (mul_le_mul_of_nonneg_left hmoment_bound (by positivity))
      _ ≤ (2 * Real.pi * (M * (B * R))) * ‖E.toContinuousLinearMap‖ := by
        gcongr
      _ = ((2 * Real.pi * M) * B * ‖E.toContinuousLinearMap‖) * R := by ring


/-- The representative also obeys a Euclidean coordinate-gradient bound. -/
theorem u8_physical_high_weak_derivatives_C1_euclidean_gradient
    (d : ℕ) : ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧
    ∀ (F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
      (R : ℝ), 0 ≤ R →
      (∀ p, p.length < d + 3 →
        IsPhysicalH1Graph volume (Or.inl rfl) (F p) (fun j => F (p ++ [j]))) →
      (∀ p, p.length ≤ d + 3 → ‖F p‖ ≤ R) →
      ∃ f : BoundedContinuousFunction (Vec d) ℂ,
        ContDiff ℝ 1 f ∧ (f : Vec d → ℂ) =ᵐ[volume] (F []) ∧
        ‖f‖ ≤ C * R ∧ ∀ x, Real.sqrt (∑ j : Fin d,
          ‖fderiv ℝ f x (unitVector j)‖ ^ 2) ≤ D * R := by
  obtain ⟨C, D, hC, hD, hquant⟩ := u8_physical_high_weak_derivatives_C1_quantitative d
  refine ⟨C, ((d : ℝ) + 1) * D, hC, by positivity, ?_⟩
  intro F R hR hF hbound
  obtain ⟨f, hf, hfe, hfnorm, hder⟩ := hquant F R hR hF hbound
  refine ⟨f, hf, hfe, hfnorm, ?_⟩
  intro x
  have hcoord (j : Fin d) : ‖fderiv ℝ f x (unitVector j)‖ ≤ D * R := by
    have hunit : ‖unitVector j‖ = 1 := by
      unfold unitVector
      rw [Pi.norm_single, norm_one]
    have hh : ‖fderiv ℝ f x (unitVector j)‖ ≤ ‖fderiv ℝ f x‖ := by
      simpa only [hunit, mul_one] using (fderiv ℝ f x).le_opNorm (unitVector j)
    exact hh.trans (hder x)
  have hsums : (∑ j : Fin d, ‖fderiv ℝ f x (unitVector j)‖ ^ 2) ≤
      (d : ℝ) * (D * R) ^ 2 := by
    calc
      _ ≤ ∑ _j : Fin d, (D * R) ^ 2 := Finset.sum_le_sum (fun j _ =>
        pow_le_pow_left₀ (norm_nonneg _) (hcoord j) 2)
      _ = _ := by simp
  have hdim : (d : ℝ) ≤ ((d : ℝ) + 1) ^ 2 := by
    have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
    nlinarith [sq_nonneg (d : ℝ)]
  have hprod := mul_le_mul_of_nonneg_right hdim (sq_nonneg (D * R))
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · nlinarith



/-- An L² norm bound from pointwise geometric interpolation of squared norms. -/
theorem u8_eLpNorm_two_interpolation {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {f g h : α → ℂ} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (hh : AEStronglyMeasurable h μ)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ' : θ ≤ 1)
    (hpoint : ∀ᵐ x ∂μ, ‖h x‖ₑ ^ (2 : ℝ) ≤
      (‖f x‖ₑ ^ (2 : ℝ)) ^ θ * (‖g x‖ₑ ^ (2 : ℝ)) ^ (1 - θ)) :
    eLpNorm h 2 μ ≤ (eLpNorm f 2 μ) ^ θ * (eLpNorm g 2 μ) ^ (1 - θ) := by
  have hi := ENNReal.lintegral_mul_norm_pow_le
    (hf.enorm.pow_const (2 : ℝ)) (hg.enorm.pow_const (2 : ℝ)) hθ (sub_nonneg.mpr hθ')
    (show θ + (1 - θ) = 1 by ring)
  have hli := (lintegral_mono_ae hpoint).trans hi
  have hr := ENNReal.rpow_le_rpow hli (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hh,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hg]
  norm_num only [ENNReal.toReal_ofNat] at ⊢
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul] at hr
  simpa only [← ENNReal.rpow_mul, mul_comm] using hr

/-- The L² interpolation estimate in terms of norms of L² classes. -/
theorem u8_Lp_two_interpolation {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f g h : Lp ℂ 2 μ) {θ : ℝ}
    (hθ : 0 ≤ θ) (hθ' : θ ≤ 1)
    (hpoint : ∀ᵐ x ∂μ, ‖h x‖ₑ ^ (2 : ℝ) ≤
      (‖f x‖ₑ ^ (2 : ℝ)) ^ θ * (‖g x‖ₑ ^ (2 : ℝ)) ^ (1 - θ)) :
    ‖h‖ ≤ ‖f‖ ^ θ * ‖g‖ ^ (1 - θ) := by
  have hi := u8_eLpNorm_two_interpolation μ (Lp.aestronglyMeasurable f)
    (Lp.aestronglyMeasurable g) (Lp.aestronglyMeasurable h) hθ hθ' hpoint
  have hfin : (eLpNorm f 2 μ) ^ θ * (eLpNorm g 2 μ) ^ (1 - θ) ≠ ⊤ := by
    exact (ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg hθ (Lp.eLpNorm_ne_top f))
      (ENNReal.rpow_lt_top_of_nonneg (sub_nonneg.mpr hθ') (Lp.eLpNorm_ne_top g))).ne
  have hr := ENNReal.toReal_mono hfin hi
  simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← Lp.norm_def] using hr

/-- Choose a strictly intermediate order while keeping a positive interpolation exponent. -/
theorem u8_intermediate_order_exponent {a s : ℝ} (ha : 0 ≤ a) (has : a < s) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ a < s * (1 - θ) := by
  have hs : 0 < s := lt_of_le_of_lt ha has
  let θ : ℝ := (s - a) / (2 * s)
  have hθ : 0 < θ := by
    dsimp [θ]
    exact div_pos (sub_pos.mpr has) (by positivity)
  have hθ' : θ < 1 := by
    dsimp [θ]
    rw [div_lt_one (by positivity : 0 < 2 * s)]
    linarith
  have hid : s * (1 - θ) = (s + a) / 2 := by
    dsimp [θ]
    field_simp [ne_of_gt hs]; ring
  exact ⟨θ, hθ, hθ', by rw [hid]; linarith⟩

/-- The scalar identity behind interpolation of weighted Fourier norms. -/
theorem u8_weighted_square_interpolation {a b θ : ℝ} (ha : 0 ≤ a)
    (hθ : 0 ≤ θ) (hθ' : θ ≤ 1) :
    (a ^ θ * b) ^ 2 = ((a * b) ^ 2) ^ θ * (b ^ 2) ^ (1 - θ) := by
  have ha2 : (a ^ θ) ^ 2 = (a ^ 2) ^ θ := by
    calc
      (a ^ θ) ^ 2 = a ^ (θ * 2 : ℝ) := by exact (Real.rpow_mul_natCast ha θ 2).symm
      _ = (a ^ 2) ^ θ := by rw [mul_comm]; exact Real.rpow_natCast_mul ha 2 θ
  have hb2 : (b ^ 2) ^ θ * (b ^ 2) ^ (1 - θ) = b ^ 2 := by
    rw [← Real.rpow_add_of_nonneg (sq_nonneg b) hθ (sub_nonneg.mpr hθ')]
    simp
  calc
    (a ^ θ * b) ^ 2 = (a ^ 2) ^ θ * b ^ 2 := by rw [mul_pow, ha2]
    _ = (a ^ 2) ^ θ * ((b ^ 2) ^ θ * (b ^ 2) ^ (1 - θ)) := by rw [hb2]
    _ = ((a * b) ^ 2) ^ θ * (b ^ 2) ^ (1 - θ) := by
      rw [mul_pow, Real.mul_rpow (sq_nonneg a) (sq_nonneg b)]
      ring




/-- A nonpositive power of the quadratic Fourier weight is bounded. -/
theorem u8_reciprocal_power_memLp_top {d : ℕ} {a : ℝ} (ha : 0 ≤ a) :
    MemLp (fun x : EuclideanSpace ℝ (Fin d) =>
      Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-a))) ∞ volume := by
  have ht : (fun x : EuclideanSpace ℝ (Fin d) =>
      Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-a))).HasTemperateGrowth := by
    fun_prop
  apply memLp_top_of_bound ht.1.continuous.aestronglyMeasurable 1
  filter_upwards with x
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg ‖x‖]) (by linarith)

/-- Multiplication by a reciprocal fractional weight constructs the
intermediate weighted Fourier representative from the high-order one. -/
theorem u8_intermediate_fourier_representative {d : ℕ} {s θ : ℝ}
    (hs : 0 ≤ s) (hθ : 0 ≤ θ)
    (T : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ))
    (u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hu : TemperedDistribution.smulLeftCLM ℂ
      (fun x => ((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ)) (𝓕 T) = u) :
    ∃ w : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))),
      TemperedDistribution.smulLeftCLM ℂ
        (fun x => ((1 + ‖x‖ ^ 2) ^ ((s * (1 - θ)) / 2) : ℝ)) (𝓕 T) = w ∧
      ∀ᵐ x ∂volume, w x = ((1 + ‖x‖ ^ 2) ^ (-(s * θ) / 2) : ℝ) • u x := by
  have hw := u8_reciprocal_power_memLp_top (d := d)
    (a := s * θ / 2) (by positivity)
  let w : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))) := hw.toLp _ • u
  refine ⟨w, ?_, ?_⟩
  · dsimp [w]
    rw [Lp.toTemperedDistribution_smul_eq (by fun_prop) hw, ← hu,
      TemperedDistribution.smulLeftCLM_smulLeftCLM_apply (by fun_prop) (by fun_prop)]
    congr 2
    ext x
    rw [Pi.mul_apply]
    norm_cast
    rw [← Real.rpow_add (by positivity)]
    congr 1
    ring
  · filter_upwards [Lp.coeFn_lpSMul (r := (2 : ℝ≥0∞)) (hw.toLp _) u,
      MemLp.coeFn_toLp hw] with x hx hxw
    change (w : EuclideanSpace ℝ (Fin d) → ℂ) x = (hw.toLp _) x • u x at hx
    rw [hxw] at hx
    simpa [w, neg_div] using hx

/-- The low Fourier representative is the original L² Fourier transform. -/
theorem u8_low_fourier_representative {d : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hu : TemperedDistribution.smulLeftCLM ℂ
      (fun x => ((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ))
      (𝓕 (f : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ))) = u) :
    ∀ᵐ x ∂volume, (𝓕 f) x = ((1 + ‖x‖ ^ 2) ^ (-s / 2) : ℝ) • u x := by
  obtain ⟨v, hv, hvae⟩ := u8_intermediate_fourier_representative
    (θ := 1) hs (by norm_num) (f : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) u hu
  have hv' : (𝓕 (f : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ))) = v := by
    simpa using hv
  have hveq : v = 𝓕 f := by
    apply LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot
      (F := ℂ) (μ := (volume : Measure (EuclideanSpace ℝ (Fin d)))) (p := 2))
    change (v : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) = ((𝓕 f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ))
    rw [← Lp.fourier_toTemperedDistribution_eq]
    exact hv'.symm
  simpa [hveq] using hvae

/-- The intermediate Fourier class has the geometric L² bound, provided
its low and intermediate pointwise multiplier descriptions are available. -/
theorem u8_weighted_fourier_interpolation {d : ℕ} {s θ : ℝ}
    (hθ : 0 ≤ θ) (hθ' : θ ≤ 1)
    (v u w : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hv : ∀ᵐ x ∂volume, v x = ((1 + ‖x‖ ^ 2) ^ (-s / 2) : ℝ) • u x)
    (hw : ∀ᵐ x ∂volume, w x = ((1 + ‖x‖ ^ 2) ^ (-(s * θ) / 2) : ℝ) • u x) :
    ‖w‖ ≤ ‖v‖ ^ θ * ‖u‖ ^ (1 - θ) := by
  apply u8_Lp_two_interpolation volume v u w hθ hθ'
  filter_upwards [hv, hw] with x hvx hwx
  let a : ℝ := (1 + ‖x‖ ^ 2) ^ (-s / 2)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hweight : (1 + ‖x‖ ^ 2) ^ (-(s * θ) / 2) = a ^ θ := by
    dsimp [a]
    rw [← Real.rpow_mul (by positivity)]
    congr 1
    ring
  have hvnorm : ‖v x‖ = a * ‖u x‖ := by
    rw [hvx, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
  have hwnorm : ‖w x‖ = a ^ θ * ‖u x‖ := by
    rw [hwx, hweight, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg ha _)]
  have hreal : ‖w x‖ ^ 2 = (‖v x‖ ^ 2) ^ θ * (‖u x‖ ^ 2) ^ (1 - θ) := by
    rw [hwnorm, hvnorm]
    exact u8_weighted_square_interpolation ha hθ hθ'
  have henn := congrArg ENNReal.ofReal hreal
  simpa only [← ENNReal.ofReal_rpow_of_nonneg (sq_nonneg ‖v x‖) hθ,
    ← ENNReal.ofReal_rpow_of_nonneg (sq_nonneg ‖u x‖) (sub_nonneg.mpr hθ'),
    ENNReal.ofReal_mul (Real.rpow_nonneg (sq_nonneg ‖v x‖) θ),
    ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ← ENNReal.rpow_natCast, Nat.cast_ofNat] using henn.le

/-- Intermediate Fourier representative controlled by the low and high L² norms. -/
theorem u8_intermediate_fourier_norm {d : ℕ} {s θ : ℝ}
    (hs : 0 ≤ s) (hθ : 0 ≤ θ) (hθ' : θ ≤ 1)
    (f u : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hu : TemperedDistribution.smulLeftCLM ℂ
      (fun x => ((1 + ‖x‖ ^ 2) ^ (s / 2) : ℝ))
      (𝓕 (f : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ))) = u) :
    ∃ w : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))),
      TemperedDistribution.smulLeftCLM ℂ
        (fun x => ((1 + ‖x‖ ^ 2) ^ ((s * (1 - θ)) / 2) : ℝ))
        (𝓕 (f : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ))) = w ∧
      ‖w‖ ≤ ‖f‖ ^ θ * ‖u‖ ^ (1 - θ) := by
  obtain ⟨w, hw, hpoint⟩ := u8_intermediate_fourier_representative
    hs hθ (f : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) u hu
  have hlow := u8_low_fourier_representative hs f u hu
  refine ⟨w, hw, ?_⟩
  have hbound := u8_weighted_fourier_interpolation hθ hθ' (𝓕 f) u w hlow hpoint
  simpa only [Lp.norm_fourier_eq] using hbound

/-- Transfer the high-order bound through the nonnegative interpolation power. -/
theorem u8_interpolation_high_norm_bound {n h B R θ : ℝ}
    (hn : 0 ≤ n) (hh : 0 ≤ h) (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hθ : θ ≤ 1) (hbound : h ≤ B * R) :
    n ^ θ * h ^ (1 - θ) ≤ (B + 1) ^ (1 - θ) *
      (n ^ θ * R ^ (1 - θ)) := by
  have hBR : h ≤ (B + 1) * R := by nlinarith
  have hpow := Real.rpow_le_rpow hh hBR (sub_nonneg.mpr hθ)
  have hpow' := mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hn θ)
  rw [Real.mul_rpow (by positivity : 0 ≤ B + 1) hR] at hpow'
  calc
    n ^ θ * h ^ (1 - θ) ≤ n ^ θ * ((B + 1) ^ (1 - θ) * R ^ (1 - θ)) := hpow'
    _ = (B + 1) ^ (1 - θ) * (n ^ θ * R ^ (1 - θ)) := by ring




/-- Global quantitative C¹ interpolation for a finite weak-derivative chain. -/
theorem u8_physical_C1_interpolation (d : ℕ) :
    ∃ C D θ : ℝ, 0 < C ∧ 0 ≤ D ∧ 0 < θ ∧ θ < 1 ∧
    ∀ (F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
      (R : ℝ), 0 ≤ R →
      (∀ p, p.length < d + 3 →
        IsPhysicalH1Graph volume (Or.inl rfl) (F p) (fun j => F (p ++ [j]))) →
      (∀ p, p.length ≤ d + 3 → ‖F p‖ ≤ R) →
      ∃ f : BoundedContinuousFunction (Vec d) ℂ,
        ContDiff ℝ 1 f ∧ (f : Vec d → ℂ) =ᵐ[volume] (F []) ∧
        ‖f‖ ≤ C * (‖F []‖ ^ θ * R ^ (1 - θ)) ∧
        ∀ x, ‖fderiv ℝ f x‖ ≤ D * (‖F []‖ ^ θ * R ^ (1 - θ)) := by
  obtain ⟨k, hk, hk'⟩ := u8_sobolev_even_order d
  have hs : (d : ℝ) / 2 + 1 < 2 * (k : ℝ) := by
    have h : (d : ℝ) + 2 < 4 * (k : ℝ) := by exact_mod_cast hk'
    linarith
  obtain ⟨θ, hθ, hθ1, hθs⟩ := u8_intermediate_order_exponent
    (show 0 ≤ (d : ℝ) / 2 + 1 by positivity) hs
  have hs' : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) <
      2 * ((2 * (k : ℝ)) * (1 - θ) - 1) := by
    simp only [finrank_euclideanSpace_fin]
    linarith
  obtain ⟨K, M, hK, hM, hfourier⟩ := u8_euclidean_fourier_L1_quantitative hs'
  let B : ℝ := (1 + (d : ℝ) * ((2 * Real.pi) ^ 2 : ℝ)⁻¹) ^ k
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let A : ℝ := (B + 1) ^ (1 - θ)
  have hA : 0 < A := by dsimp [A]; positivity
  let E := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  refine ⟨(K + 1) * (A + 1), (2 * Real.pi * M) * A * ‖E.toContinuousLinearMap‖,
    θ, by positivity, by positivity, hθ, hθ1, ?_⟩
  intro F R hR hF hbound
  let J : EuclideanSpace ℝ (Fin d) → Vec d := WithLp.ofLp
  let hJ : MeasurePreserving J volume volume := PiLp.volume_preserving_ofLp (Fin d)
  let f0 := Lp.compMeasurePreserving J hJ (F [])
  let u := 𝓕 (u8EuclideanBesselChain F k [])
  have hpot : TemperedDistribution.besselPotential (EuclideanSpace ℝ (Fin d)) ℂ
      (2 * (k : ℝ)) (f0 : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) =
      (u8EuclideanBesselChain F k [] : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) := by
    exact u8EuclideanBesselChain_represents F hF k [] (by simpa using hk)
  have hu : TemperedDistribution.smulLeftCLM ℂ
      (fun x => ((1 + ‖x‖ ^ 2) ^ ((2 * (k : ℝ)) / 2) : ℝ))
      (𝓕 (f0 : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ))) = u := by
    rw [← TemperedDistribution.fourier_besselPotential_eq_smulLeftCLM_fourier_apply,
      hpot, Lp.fourier_toTemperedDistribution_eq]
  obtain ⟨w, hw, hwnorm⟩ := u8_intermediate_fourier_norm
    (show 0 ≤ 2 * (k : ℝ) by positivity) hθ.le hθ1.le f0 u hu
  obtain ⟨v, hv, hvnorm, hmoment, hmoment_bound⟩ :=
    hfourier (f0 : 𝓢'(EuclideanSpace ℝ (Fin d), ℂ)) w hw
  have hvC1 := u8_euclidean_inverse_fourier_C1 v hmoment
  have hvae := u8_euclidean_inverse_fourier_ae f0 v hv
  have htransport : (f0 : EuclideanSpace ℝ (Fin d) → ℂ) =ᵐ[volume]
      fun x => F [] (J x) := Lp.coeFn_compMeasurePreserving (F []) hJ
  let Ec : C(Vec d, EuclideanSpace ℝ (Fin d)) := ⟨E, E.continuous⟩
  let f := (Real.Lp.fourierTransformInv v).compContinuous Ec
  have hp := c18_euclidean_C1_representative_pullback
    (Real.Lp.fourierTransformInv v) (F []) hvC1 (hvae.trans htransport)
  have hf : ContDiff ℝ 1 f := by
    simpa [f, Ec, E, PiLp.coe_symm_continuousLinearEquiv, Function.comp_def] using hp.1
  have hfe : (f : Vec d → ℂ) =ᵐ[volume] (F []) := by
    simpa [f, Ec, E, PiLp.coe_symm_continuousLinearEquiv, Function.comp_def] using hp.2.1
  have hfnorm : ‖f‖ ≤ ‖Real.Lp.fourierTransformInv v‖ :=
    BoundedContinuousFunction.norm_compContinuous_le _ _
  have hunorm : ‖u‖ ≤ B * R := by
    dsimp [u, B]
    rw [Lp.norm_fourier_eq]
    exact u8EuclideanBesselChain_norm_le F R hbound k [] (by simpa using hk)
  let P : ℝ := ‖F []‖ ^ θ * R ^ (1 - θ)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hwbound : ‖w‖ ≤ A * P := by
    have hnormf : ‖f0‖ = ‖F []‖ := Lp.norm_compMeasurePreserving (F []) hJ
    rw [hnormf] at hwnorm
    exact hwnorm.trans (u8_interpolation_high_norm_bound (norm_nonneg _) (norm_nonneg _)
      hB hR hθ1.le hunorm)
  refine ⟨f, hf, hfe, ?_, ?_⟩
  · have hfac : K * A ≤ (K + 1) * (A + 1) := by nlinarith
    calc
      ‖f‖ ≤ ‖Real.Lp.fourierTransformInv v‖ := hfnorm
      _ ≤ ‖v‖ := u8_euclidean_inverse_fourier_norm_le v
      _ ≤ K * ‖w‖ := hvnorm
      _ ≤ K * (A * P) := mul_le_mul_of_nonneg_left hwbound hK
      _ = (K * A) * P := by ring
      _ ≤ ((K + 1) * (A + 1)) * P := mul_le_mul_of_nonneg_right hfac hP
  · intro x
    have hcomp : (f : Vec d → ℂ) = (fun z => Real.Lp.fourierTransformInv v (E z)) := by rfl
    rw [hcomp]
    change ‖fderiv ℝ ((fun z => Real.Lp.fourierTransformInv v z) ∘ E) x‖ ≤ _
    rw [fderiv_comp x (hvC1.differentiable (by norm_num) _) E.differentiableAt]
    change ‖fderiv ℝ (fun z => Real.Lp.fourierTransformInv v z) (E x) ∘SL
      fderiv ℝ (fun z => E.toContinuousLinearMap z) x‖ ≤ _
    rw [E.toContinuousLinearMap.fderiv]
    calc
      _ ≤ ‖fderiv ℝ (fun z => Real.Lp.fourierTransformInv v z) (E x)‖ *
          ‖E.toContinuousLinearMap‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (2 * Real.pi * (M * ‖w‖)) * ‖E.toContinuousLinearMap‖ := by
        gcongr
        exact (u8_euclidean_inverse_fourier_derivative_bound v hmoment (E x)).trans
          (mul_le_mul_of_nonneg_left hmoment_bound (by positivity))
      _ ≤ (2 * Real.pi * (M * (A * P))) * ‖E.toContinuousLinearMap‖ := by gcongr
      _ = ((2 * Real.pi * M) * A * ‖E.toContinuousLinearMap‖) * P := by ring


/-- The interpolated derivative bound in Euclidean coordinate norm. -/
theorem u8_physical_C1_interpolation_gradient (d : ℕ) :
    ∃ C D θ : ℝ, 0 < C ∧ 0 ≤ D ∧ 0 < θ ∧ θ < 1 ∧
    ∀ (F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
      (R : ℝ), 0 ≤ R →
      (∀ p, p.length < d + 3 →
        IsPhysicalH1Graph volume (Or.inl rfl) (F p) (fun j => F (p ++ [j]))) →
      (∀ p, p.length ≤ d + 3 → ‖F p‖ ≤ R) →
      ∃ f : BoundedContinuousFunction (Vec d) ℂ,
        ContDiff ℝ 1 f ∧ (f : Vec d → ℂ) =ᵐ[volume] (F []) ∧
        ‖f‖ ≤ C * (‖F []‖ ^ θ * R ^ (1 - θ)) ∧
        ∀ x, Real.sqrt (∑ j : Fin d, ‖fderiv ℝ f x (unitVector j)‖ ^ 2) ≤
          D * (‖F []‖ ^ θ * R ^ (1 - θ)) := by
  obtain ⟨C, D, θ, hC, hD, hθ, hθ1, hquant⟩ :=
    u8_physical_C1_interpolation d
  refine ⟨C, ((d : ℝ) + 1) * D, θ, hC, by positivity, hθ, hθ1, ?_⟩
  intro F R hR hF hbound
  obtain ⟨f, hf, hfe, hfnorm, hder⟩ := hquant F R hR hF hbound
  refine ⟨f, hf, hfe, hfnorm, ?_⟩
  intro x
  let P : ℝ := ‖F []‖ ^ θ * R ^ (1 - θ)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hcoord (j : Fin d) : ‖fderiv ℝ f x (unitVector j)‖ ≤ D * P := by
    have hunit : ‖unitVector j‖ = 1 := by
      unfold unitVector
      rw [Pi.norm_single, norm_one]
    have hh : ‖fderiv ℝ f x (unitVector j)‖ ≤ ‖fderiv ℝ f x‖ := by
      simpa only [hunit, mul_one] using (fderiv ℝ f x).le_opNorm (unitVector j)
    exact hh.trans (hder x)
  have hsums : (∑ j : Fin d, ‖fderiv ℝ f x (unitVector j)‖ ^ 2) ≤
      (d : ℝ) * (D * P) ^ 2 := by
    calc
      _ ≤ ∑ _j : Fin d, (D * P) ^ 2 := Finset.sum_le_sum (fun j _ =>
        pow_le_pow_left₀ (norm_nonneg _) (hcoord j) 2)
      _ = _ := by simp
  have hdim : (d : ℝ) ≤ ((d : ℝ) + 1) ^ 2 := by
    have hd : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
    nlinarith [sq_nonneg (d : ℝ)]
  have hprod := mul_le_mul_of_nonneg_right hdim (sq_nonneg (D * P))
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · nlinarith


/-- Global interpolation for every C¹ representative of the chain. -/
theorem u8_global_C1_interpolation_of_weak_derivative_chain :
    ∀ d : ℕ, ∃ K θ : ℝ, 0 < K ∧ 0 < θ ∧ θ < 1 ∧
      ∀ (F : List (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)))
        (R : ℝ), 0 ≤ R →
        (∀ p, p.length < d + 3 → IsPhysicalH1Graph volume (Or.inl rfl)
          (F p) (fun j => F (p ++ [j]))) →
        (∀ p, p.length ≤ d + 3 → ‖F p‖ ≤ R) →
        ∀ u : Vec d → ℂ, ContDiff ℝ 1 u → u =ᵐ[volume] (F []) →
        ∀ x : Vec d,
          ‖u x‖ + Real.sqrt (∑ j : Fin d,
            ‖fderiv ℝ u x (unitVector j)‖ ^ 2) ≤
            K * (‖F []‖ ^ θ * R ^ (1 - θ) + ‖F []‖) := by
  intro d
  obtain ⟨C, D, θ, hC, hD, hθ, hθ1, hquant⟩ :=
    u8_physical_C1_interpolation_gradient d
  refine ⟨C + D + 1, θ, by positivity, hθ, hθ1, ?_⟩
  intro F R hR hF hbound u hu hue x
  obtain ⟨f, hf, hfe, hfnorm, hgrad⟩ := hquant F R hR hF hbound
  have heq : u = (f : Vec d → ℂ) :=
    Measure.eq_of_ae_eq (hue.trans hfe.symm) hu.continuous f.continuous
  rw [heq]
  let P : ℝ := ‖F []‖ ^ θ * R ^ (1 - θ)
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hpoint : ‖f x‖ ≤ C * P := (f.norm_coe_le_norm x).trans hfnorm
  have hg := hgrad x
  have hn : 0 ≤ ‖F []‖ := norm_nonneg _
  nlinarith


end EinsteinFull
