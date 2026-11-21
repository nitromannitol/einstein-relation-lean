import EinsteinFull.Homogenization.HeatHessianL2

/-!
# Small-time convergence of the heat Hessian on `L²`

For `f ∈ L²(ℝ^d)` the heat smoothings `Φ_ε * f` converge to `f` in `L²` as `ε → 0`, and the
time-truncated heat Hessian satisfies `‖∫_{ε₁}^{ε₂} ∂ⱼ∂ᵢΦ_t * f dt‖₂ ≤ ‖Φ_{ε₂} * f - Φ_{ε₁} * f‖₂`.
Both follow from the smooth case by density of smooth compactly supported functions. Hence the
truncations of the heat formula (6.7) in Armstrong, Kuusi and Mourrat, *Quantitative Stochastic
Homogenization and Large-Scale Regularity*, at small times are Cauchy in `L²`.
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff

namespace EinsteinFull.Homogenization

open EinsteinRelation EinsteinRelation.Correctors

variable {d : ℕ}

/-- A smooth compactly supported approximation in `L²`. -/
theorem exists_smoothCompact_eLpNorm_sub_le {f : Vec d → ℝ} (hf : MemLp f 2 volume) {η : ℝ}
    (hη : 0 < η) :
    ∃ ψ : Vec d → ℝ, IsSmoothCompact ψ ∧ eLpNorm (f - ψ) 2 volume ≤ ENNReal.ofReal η := by
  obtain ⟨ψ, hψc, hψs, hψ⟩ := hf.exist_eLpNorm_sub_le (by norm_num) (by norm_num) hη
  exact ⟨ψ, ⟨hψs, hψc⟩, hψ⟩

/-- The heat semigroup is continuous at time zero on `L²`. -/
theorem tendsto_eLpNorm_heatConv_sub {f : Vec d → ℝ} (hfm : Measurable f)
    (hf : MemLp f 2 volume) :
    Tendsto (fun ε => eLpNorm (fun x => heatConv ε f x - f x) 2 volume) (𝓝[>] 0) (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  have hδ3 : 0 < δ / 3 := ENNReal.div_pos hδ.ne' (by norm_num)
  obtain ⟨r, hr0, hr1, hr2⟩ := ENNReal.lt_iff_exists_real_btwn.mp hδ3
  have hr : 0 < r := by
    rcases hr0.lt_or_eq with h | h
    · exact h
    · rw [← h, ENNReal.ofReal_zero] at hr1
      exact absurd hr1 (lt_irrefl 0)
  obtain ⟨ψ, hψ, hfψ⟩ := exists_smoothCompact_eLpNorm_sub_le hf hr
  have hψm := hψ.1.continuous.measurable
  have hlim := (ENNReal.tendsto_nhds_zero.mp (tendsto_eLpNorm_heatConv_sub_of_smooth hψ))
    (δ / 3) hδ3
  filter_upwards [hlim, self_mem_nhdsWithin] with ε hε hε0
  have hsplit : (fun x => heatConv ε f x - f x) =
      (fun x => heatConv ε f x - heatConv ε ψ x) + (fun x => heatConv ε ψ x - ψ x) + (ψ - f) := by
    funext x
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  rw [hsplit]
  calc eLpNorm ((fun x => heatConv ε f x - heatConv ε ψ x) + (fun x => heatConv ε ψ x - ψ x) +
        (ψ - f)) 2 volume
      ≤ eLpNorm (fun x => heatConv ε f x - heatConv ε ψ x) 2 volume +
          eLpNorm (fun x => heatConv ε ψ x - ψ x) 2 volume + eLpNorm (ψ - f) 2 volume :=
        (eLpNorm_add_le (p := 2) (by norm_num)).trans
          (add_le_add (eLpNorm_add_le (p := 2) (by norm_num)) le_rfl)
    _ ≤ δ / 3 + δ / 3 + δ / 3 := by
        gcongr
        · exact (eLpNorm_heatConv_sub_le hε0 hfm hf hψm hψ.memLp).trans (hfψ.trans hr2.le)
        · rw [eLpNorm_sub_comm]
          exact hfψ.trans hr2.le
    _ = δ := ENNReal.add_thirds δ

/-- **`L²` bound of the time-truncated heat Hessian** by the difference of heat smoothings. -/
theorem eLpNorm_heatHessianWindow_le {ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁) (hε : ε₁ ≤ ε₂) (i j : Fin d)
    {f : Vec d → ℝ} (hfm : Measurable f) (hf : MemLp f 2 volume) :
    eLpNorm (heatHessianWindow ε₁ ε₂ i j f) 2 volume ≤
      eLpNorm (fun x => heatConv ε₂ f x - heatConv ε₁ f x) 2 volume := by
  have hε₂ : 0 < ε₂ := lt_of_lt_of_le hε₁ hε
  set C : ℝ := (ε₂ - ε₁) * windowHessianConst d ε₁ ε₂ with hC
  have hC0 : 0 ≤ C := mul_nonneg (by linarith) (windowHessianConst_nonneg hε₁ hε)
  refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
  set η : ℝ := (δ : ℝ) / (C + 2) with hη
  have hη0 : 0 < η := div_pos (by exact_mod_cast hδ) (by linarith)
  have hηδ : C * η + η + η = δ := by
    rw [hη]
    field_simp
    ring
  obtain ⟨ψ, hψ, hfψ⟩ := exists_smoothCompact_eLpNorm_sub_le hf hη0
  have hψm := hψ.1.continuous.measurable
  have hψ2 := hψ.memLp
  have hsplit : heatHessianWindow ε₁ ε₂ i j f =
      heatHessianWindow ε₁ ε₂ i j (f - ψ) + heatHessianWindow ε₁ ε₂ i j ψ := by
    funext x
    rw [Pi.add_apply, heatHessianWindow_sub hε₁ i j hfm hf hψm hψ2 x]
    ring
  have hsplit' : (fun x => heatConv ε₂ ψ x - heatConv ε₁ ψ x) =
      (fun x => heatConv ε₂ f x - heatConv ε₁ f x) + (fun x => heatConv ε₂ ψ x - heatConv ε₂ f x) +
        (fun x => heatConv ε₁ f x - heatConv ε₁ ψ x) := by
    funext x
    simp only [Pi.add_apply]
    ring
  have hψf : eLpNorm (ψ - f) 2 volume ≤ ENNReal.ofReal η := by
    rw [eLpNorm_sub_comm]
    exact hfψ
  have hsmooth : eLpNorm (heatHessianWindow ε₁ ε₂ i j ψ) 2 volume ≤
      eLpNorm (fun x => heatConv ε₂ f x - heatConv ε₁ f x) 2 volume + ENNReal.ofReal η +
        ENNReal.ofReal η := by
    refine (eLpNorm_heatHessianWindow_le_of_smooth hε₁ hε i j hψ).trans ?_
    rw [hsplit']
    refine (eLpNorm_add_le (by norm_num)).trans ?_
    refine add_le_add ((eLpNorm_add_le (p := 2) (by norm_num)).trans (add_le_add le_rfl ?_)) ?_
    · exact (eLpNorm_heatConv_sub_le hε₂ hψm hψ2 hfm hf).trans hψf
    · exact (eLpNorm_heatConv_sub_le hε₁ hfm hf hψm hψ2).trans hfψ
  have hcrude := eLpNorm_heatHessianWindow_le_crude hε₁ hε i j (hfm.sub hψm) (hf.sub hψ2)
  rw [hsplit]
  calc eLpNorm (heatHessianWindow ε₁ ε₂ i j (f - ψ) + heatHessianWindow ε₁ ε₂ i j ψ) 2 volume
      ≤ eLpNorm (heatHessianWindow ε₁ ε₂ i j (f - ψ)) 2 volume +
          eLpNorm (heatHessianWindow ε₁ ε₂ i j ψ) 2 volume := eLpNorm_add_le (by norm_num)
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal η +
          (eLpNorm (fun x => heatConv ε₂ f x - heatConv ε₁ f x) 2 volume + ENNReal.ofReal η +
            ENNReal.ofReal η) :=
        add_le_add (hcrude.trans (by gcongr)) hsmooth
    _ = eLpNorm (fun x => heatConv ε₂ f x - heatConv ε₁ f x) 2 volume +
          ENNReal.ofReal (C * η + η + η) := by
        rw [ENNReal.ofReal_add (by positivity) hη0.le, ENNReal.ofReal_add (by positivity) hη0.le,
          ENNReal.ofReal_mul hC0]
        ring
    _ = eLpNorm (fun x => heatConv ε₂ f x - heatConv ε₁ f x) 2 volume + δ := by
        rw [hηδ, ENNReal.ofReal_coe_nnreal]

/-- **Small-time Cauchy property** of the time-truncated heat Hessian on `L²`. -/
theorem exists_eLpNorm_heatHessianWindow_le {f : Vec d → ℝ} (hfm : Measurable f)
    (hf : MemLp f 2 volume) (i j : Fin d) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε₁ ε₂ : ℝ, 0 < ε₁ → ε₁ ≤ ε₂ → ε₂ ≤ η →
      eLpNorm (heatHessianWindow ε₁ ε₂ i j f) 2 volume ≤ δ := by
  have hδ2 : 0 < δ / 2 := ENNReal.div_pos hδ.ne' (by norm_num)
  have hev := (ENNReal.tendsto_nhds_zero.mp (tendsto_eLpNorm_heatConv_sub hfm hf)) (δ / 2) hδ2
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  refine ⟨u / 2, by have : (0 : ℝ) < u := hu; positivity, fun ε₁ ε₂ hε₁ hε hε₂ => ?_⟩
  have hu0 : (0 : ℝ) < u := hu
  have hmem : ∀ ε, 0 < ε → ε ≤ u / 2 →
      eLpNorm (fun x => heatConv ε f x - f x) 2 volume ≤ δ / 2 := fun ε h0 h1 =>
    hsub ⟨h0, by linarith⟩
  refine (eLpNorm_heatHessianWindow_le hε₁ hε i j hfm hf).trans ?_
  have hsplit : (fun x => heatConv ε₂ f x - heatConv ε₁ f x) =
      (fun x => heatConv ε₂ f x - f x) - (fun x => heatConv ε₁ f x - f x) := by
    funext x
    simp only [Pi.sub_apply]
    ring
  rw [hsplit]
  calc eLpNorm ((fun x => heatConv ε₂ f x - f x) - (fun x => heatConv ε₁ f x - f x)) 2 volume
      ≤ eLpNorm (fun x => heatConv ε₂ f x - f x) 2 volume +
          eLpNorm (fun x => heatConv ε₁ f x - f x) 2 volume := eLpNorm_sub_le (by norm_num)
    _ ≤ δ / 2 + δ / 2 :=
        add_le_add (hmem ε₂ (lt_of_lt_of_le hε₁ hε) hε₂) (hmem ε₁ hε₁ (hε.trans hε₂))
    _ = δ := ENNReal.add_halves δ

end EinsteinFull.Homogenization
