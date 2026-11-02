import EinsteinFull.Calculus.ParabolicBridgeMollConv

/-!
# The delayed time mollification

`MolS ε F (y, t) = Mol ε F (y, t - ε) = ∫ tmoll ε (t - ε - s) F (y, s) ds` only uses values of `F`
at times `s ∈ (t - 2ε, t)`.  We prove the `L²` contraction and `L²` convergence.
-/

open scoped ENNReal

noncomputable section
namespace EinsteinFull.ParabolicBridge

open MeasureTheory Set Filter Topology PDE

variable {d : ℕ}

/-- Translation of the time variable by `-a`. -/
def shiftT (a : ℝ) : Vec d × ℝ → Vec d × ℝ := fun z => (z.1, z.2 - a)

theorem shiftT_measurable (a : ℝ) : Measurable (shiftT (d := d) a) :=
  measurable_fst.prodMk (measurable_snd.sub_const a)

theorem shiftT_measurePreserving (a : ℝ) :
    MeasurePreserving (shiftT (d := d) a) volume volume := by
  have h : MeasurePreserving (Prod.map (id : Vec d → Vec d) (fun t : ℝ => t - a))
      (volume.prod volume) (volume.prod volume) :=
    (MeasurePreserving.id volume).prod (measurePreserving_sub_right volume a)
  rw [Measure.volume_eq_prod]
  exact h

/-- Delayed time mollification. -/
def MolS (ε : ℝ) (hε : 0 < ε) (F : Vec d × ℝ → ℝ) : Vec d × ℝ → ℝ :=
  fun z => Mol ε hε F (shiftT (2 * ε) z)

theorem MolS_apply {ε : ℝ} (hε : 0 < ε) (F : Vec d × ℝ → ℝ) (z : Vec d × ℝ) :
    MolS ε hε F z = ∫ s, tmoll ε hε (z.2 - 2 * ε - s) * F (z.1, s) := rfl

theorem MolS_measurable {ε : ℝ} {hε : 0 < ε} (F : Vec d × ℝ → ℝ) (hF : Measurable F) :
    Measurable (MolS ε hε F) :=
  (Mol_measurable F hF).comp (shiftT_measurable (2 * ε))

theorem eLpNorm_MolS_le {ε : ℝ} {hε : 0 < ε} (F : Vec d × ℝ → ℝ) (hF : Measurable F) :
    eLpNorm (MolS ε hε F) 2 volume ≤ eLpNorm F 2 volume := by
  have h : MolS ε hε F = Mol ε hε F ∘ shiftT (2 * ε) := rfl
  rw [h, eLpNorm_comp_measurePreserving (Mol_measurable F hF).aestronglyMeasurable
    (shiftT_measurePreserving (2 * ε))]
  exact eLpNorm_Mol_le F hF

/-- A compact box containing all shifted supports. -/
theorem exists_box (g : Vec d × ℝ → ℝ) (hc : HasCompactSupport g) :
    ∃ K : Set (Vec d × ℝ), IsCompact K ∧ ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 → ∀ x : Vec d × ℝ,
      g (shiftT ε x) ≠ 0 → x ∈ K := by
  have hKc : IsCompact (tsupport g) := hc
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ x ∈ tsupport g, ‖x.2‖ ≤ R :=
    hKc.exists_bound_of_continuousOn (f := fun x : Vec d × ℝ => x.2) continuous_snd.continuousOn
  refine ⟨(Prod.fst '' tsupport g) ×ˢ Set.Icc (-(R + 1)) (R + 1),
    (hKc.image continuous_fst).prod isCompact_Icc, ?_⟩
  intro ε hε0 hε1 x hx
  have hx' : shiftT ε x ∈ tsupport g := subset_tsupport g hx
  have h2 := hR _ hx'
  simp only [shiftT, Real.norm_eq_abs] at h2
  refine ⟨⟨_, hx', rfl⟩, ?_⟩
  rw [Set.mem_Icc]
  have := abs_le.mp h2
  constructor <;> linarith [this.1, this.2]

/-- Translation continuity in `L²` for a compactly supported continuous function. -/
theorem eLpNorm_shift_sub_cont (g : Vec d × ℝ → ℝ) (hg : Continuous g) (hc : HasCompactSupport g)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      eLpNorm (fun z => g (shiftT ε z) - g z) 2 volume ≤ ENNReal.ofReal δ := by
  obtain ⟨K, hK, hKs⟩ := exists_box g hc
  have hV : volume K < ⊤ := hK.measure_lt_top
  set W : ℝ≥0∞ := volume K ^ (1 / (2 : ℝ≥0∞).toReal) with hW
  have hWtop : W ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hV.ne
  set w : ℝ := W.toReal with hw
  have hw0 : 0 ≤ w := ENNReal.toReal_nonneg
  have hη : 0 < δ / (w + 1) := by positivity
  have huc := hc.uniformContinuous_of_continuous hg
  obtain ⟨δ', hδ', hδ''⟩ := Metric.uniformContinuous_iff.mp huc _ hη
  refine ⟨min δ' 1, lt_min hδ' one_pos, fun ε hε hεε => ?_⟩
  have hεa : ε < δ' := lt_of_lt_of_le hεε (min_le_left _ _)
  have hεb : ε ≤ 1 := (lt_of_lt_of_le hεε (min_le_right _ _)).le
  have hmeas : AEStronglyMeasurable
      ((fun z => g (shiftT ε z)) - g) volume :=
    ((hg.measurable.comp (shiftT_measurable ε)).sub hg.measurable).aestronglyMeasurable
  have hbound := eLpNorm_sub_le_of_dist_bdd (p := 2) (s := K) (f := fun z => g (shiftT ε z))
    (g := g) volume (by simp) hK.measurableSet.nullMeasurableSet hη.le hmeas
    (fun x => by
      rw [Real.dist_eq]
      have hd : dist (shiftT ε x) x < δ' := by
        have e : dist (shiftT ε x) x = ε := by
          rw [Prod.dist_eq]
          simp [shiftT, abs_of_pos hε, hε.le]
        rw [e]; exact hεa
      have := hδ'' hd
      rw [Real.dist_eq] at this
      exact this.le)
    (fun x hx => hKs ε hε.le hεb x hx)
    (fun x hx => hKs 0 le_rfl zero_le_one x (by simpa [shiftT] using hx))
  refine hbound.trans ?_
  have hWeq : volume K ^ (1 / (2 : ℝ≥0∞).toReal) = ENNReal.ofReal w := by
    rw [hw, ENNReal.ofReal_toReal hWtop]
  rw [hWeq, ← ENNReal.ofReal_mul hη.le]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith

/-- Translation continuity in `L²`. -/
theorem eLpNorm_shift_sub_tendsto (F : Vec d × ℝ → ℝ) (hF : Measurable F)
    (hFl : ∫⁻ z, ‖F z‖ₑ ^ (2 : ℝ) ≠ ⊤) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      eLpNorm (fun z => F (shiftT ε z) - F z) 2 volume ≤ ENNReal.ofReal δ := by
  have hF2 : MemLp F 2 volume := (eLpNorm_two_lt_top_iff hF.aestronglyMeasurable).mpr hFl
  have hδ3 : 0 < δ / 3 := by positivity
  obtain ⟨g, hgc, hFg, hgcont, hgmem⟩ := hF2.exists_hasCompactSupport_eLpNorm_sub_le
    (by simp : (2 : ℝ≥0∞) ≠ ∞) (ε := ENNReal.ofReal (δ / 3))
    (ENNReal.ofReal_pos.mpr hδ3).ne'
  have hgm : Measurable g := hgcont.measurable
  have hFgm : Measurable (F - g) := hF.sub hgm
  obtain ⟨ε₀, hε₀, hε₀'⟩ := eLpNorm_shift_sub_cont g hgcont hgc hδ3
  refine ⟨ε₀, hε₀, fun ε hε hεε₀ => ?_⟩
  have hsub : (fun z => F (shiftT ε z) - F z) =
      fun z => (F - g) (shiftT ε z) + (g (shiftT ε z) - g z) - (F - g) z := by
    funext z
    simp only [Pi.sub_apply]
    ring
  have ha : eLpNorm (fun z => (F - g) (shiftT ε z)) 2 volume = eLpNorm (F - g) 2 volume :=
    eLpNorm_comp_measurePreserving hFgm.aestronglyMeasurable (shiftT_measurePreserving ε)
  have hb := hε₀' ε hε hεε₀
  rw [hsub]
  calc eLpNorm (fun z => (F - g) (shiftT ε z) + (g (shiftT ε z) - g z) - (F - g) z) 2 volume
      ≤ eLpNorm (fun z => (F - g) (shiftT ε z) + (g (shiftT ε z) - g z)) 2 volume +
          eLpNorm (F - g) 2 volume := eLpNorm_sub_le (f := fun z => (F - g) (shiftT ε z) +
            (g (shiftT ε z) - g z)) (g := F - g) (by norm_num)
    _ ≤ (eLpNorm (fun z => (F - g) (shiftT ε z)) 2 volume +
          eLpNorm (fun z => g (shiftT ε z) - g z) 2 volume) + eLpNorm (F - g) 2 volume :=
        add_le_add_left (eLpNorm_add_le (by norm_num)) _
    _ ≤ (ENNReal.ofReal (δ / 3) + ENNReal.ofReal (δ / 3)) + ENNReal.ofReal (δ / 3) := by
        rw [ha]
        exact add_le_add (add_le_add hFg hb) hFg
    _ = ENNReal.ofReal δ := by
        rw [← ENNReal.ofReal_add hδ3.le hδ3.le, ← ENNReal.ofReal_add (by positivity) hδ3.le]
        congr 1
        ring

/-- `L²` convergence of the delayed time mollification. -/
theorem MolS_L2_converges (F : Vec d × ℝ → ℝ) (hF : Measurable F)
    (hFl : ∫⁻ z, ‖F z‖ₑ ^ (2 : ℝ) ≠ ⊤) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ (ε : ℝ) (hε : 0 < ε), ε < ε₀ →
      eLpNorm (MolS ε hε F - F) 2 volume ≤ ENNReal.ofReal δ := by
  have hδ2 : 0 < δ / 2 := by positivity
  obtain ⟨e1, he1, h1⟩ := Mol_L2_converges F hF hFl hδ2
  obtain ⟨e2, he2, h2⟩ := eLpNorm_shift_sub_tendsto F hF hFl hδ2
  refine ⟨min e1 (e2 / 2), lt_min he1 (half_pos he2), fun ε hε hεε => ?_⟩
  have hsub : MolS ε hε F - F =
      (fun z => (Mol ε hε F - F) (shiftT (2 * ε) z)) +
        (fun z => F (shiftT (2 * ε) z) - F z) := by
    funext z
    simp only [Pi.sub_apply, Pi.add_apply, MolS]
    ring
  have ha : eLpNorm (fun z => (Mol ε hε F - F) (shiftT (2 * ε) z)) 2 volume =
      eLpNorm (Mol ε hε F - F) 2 volume :=
    eLpNorm_comp_measurePreserving
      (((Mol_measurable F hF).sub hF).aestronglyMeasurable) (shiftT_measurePreserving (2 * ε))
  have hb1 := h1 ε hε (lt_of_lt_of_le hεε (min_le_left _ _))
  have hb2 := h2 (2 * ε) (by positivity)
    (by have := lt_of_lt_of_le hεε (min_le_right _ _); linarith)
  rw [hsub]
  calc eLpNorm ((fun z => (Mol ε hε F - F) (shiftT (2 * ε) z)) +
        (fun z => F (shiftT (2 * ε) z) - F z)) 2 volume
      ≤ eLpNorm (fun z => (Mol ε hε F - F) (shiftT (2 * ε) z)) 2 volume +
          eLpNorm (fun z => F (shiftT (2 * ε) z) - F z) 2 volume :=
        eLpNorm_add_le (by norm_num)
    _ ≤ ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) := by
        rw [ha]
        exact add_le_add hb1 hb2
    _ = ENNReal.ofReal δ := by
        rw [← ENNReal.ofReal_add hδ2.le hδ2.le]
        congr 1
        ring

end EinsteinFull.ParabolicBridge
