import EinsteinFull.Homogenization.HeatFormulaLocal

/-!
# Limits of sequences that are Cauchy in `L²` on every ball

A sequence of functions on `ℝ^d` that is Cauchy in `L²(B_ρ)` for every centered ball `B_ρ` has a
limit in `L²_loc`. The limit is selected explicitly: along the indices at which the sequence is
`2^(-k)`-Cauchy on `B_k`, the sequence converges almost everywhere on every ball, and the limit is
the `limsup` along these indices. This explicit selection is used for the heat-selected flux
corrector of Armstrong, Kuusi and Mourrat, *Quantitative Stochastic Homogenization and Large-Scale
Regularity*, (6.7), whose limit must depend measurably on the coefficient field.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace EinsteinFull.Homogenization

open EinsteinRelation EinsteinRelation.External.AKM

variable {d : ℕ}

/-- A sequence that is Cauchy in `L²` on every centered ball. -/
def IsLocL2Cauchy (D : ℕ → Vec d → ℝ) : Prop :=
  ∀ ρ : ℝ, ∀ δ : ℝ≥0∞, 0 < δ → ∃ N : ℕ, ∀ p q : ℕ, N ≤ p → N ≤ q →
    eLpNorm (fun x => D p x - D q x) 2 (volume.restrict (ball 0 ρ)) ≤ δ

/-- The Cauchy property at scale `k`: `2^(-k)`-Cauchy on the ball `B_k` from `N` on. -/
def CauchyAt (D : ℕ → Vec d → ℝ) (k N : ℕ) : Prop :=
  ∀ p q : ℕ, N ≤ p → N ≤ q →
    eLpNorm (fun x => D p x - D q x) 2 (volume.restrict (ball 0 (k : ℝ))) ≤ (2⁻¹ : ℝ≥0∞) ^ k

open Classical in
/-- The first index from which the sequence is `2^(-k)`-Cauchy on `B_k`. -/
noncomputable def cauchyIndex (D : ℕ → Vec d → ℝ) (k : ℕ) : ℕ :=
  if h : ∃ N, CauchyAt D k N then Nat.find h else 0

/-- The running maximum of the Cauchy indices. -/
noncomputable def cumCauchyIndex (D : ℕ → Vec d → ℝ) (k : ℕ) : ℕ :=
  (Finset.range (k + 1)).sup (cauchyIndex D)

/-- The selected `L²_loc` limit. -/
noncomputable def locL2Limit (D : ℕ → Vec d → ℝ) (x : Vec d) : ℝ :=
  limsup (fun k => D (cumCauchyIndex D k) x) atTop

theorem CauchyAt.mono {D : ℕ → Vec d → ℝ} {k N N' : ℕ} (h : CauchyAt D k N) (hN : N ≤ N') :
    CauchyAt D k N' := fun p q hp hq => h p q (hN.trans hp) (hN.trans hq)

theorem IsLocL2Cauchy.exists_cauchyAt {D : ℕ → Vec d → ℝ} (hD : IsLocL2Cauchy D) (k : ℕ) :
    ∃ N, CauchyAt D k N :=
  hD k _ (ENNReal.pow_pos (ENNReal.inv_pos.mpr ENNReal.ofNat_ne_top) k)

theorem IsLocL2Cauchy.cauchyAt_cauchyIndex {D : ℕ → Vec d → ℝ} (hD : IsLocL2Cauchy D) (k : ℕ) :
    CauchyAt D k (cauchyIndex D k) := by
  classical
  have h := hD.exists_cauchyAt k
  simp only [cauchyIndex, h, ↓reduceDIte]
  exact Nat.find_spec h

theorem cauchyIndex_le_cumCauchyIndex (D : ℕ → Vec d → ℝ) {j k : ℕ} (hjk : j ≤ k) :
    cauchyIndex D j ≤ cumCauchyIndex D k :=
  Finset.le_sup (f := cauchyIndex D) (Finset.mem_range.mpr (Nat.lt_succ_of_le hjk))

theorem cumCauchyIndex_mono (D : ℕ → Vec d → ℝ) : Monotone (cumCauchyIndex D) := fun _ _ h =>
  Finset.sup_mono (Finset.range_subset_range.mpr (Nat.succ_le_succ h))

theorem ball_subset_ball_of_le {ρ ρ' : ℝ} (h : ρ ≤ ρ') : ball (0 : Vec d) ρ ⊆ ball 0 ρ' :=
  fun _ hx => lt_of_lt_of_le hx h

/-- From scale `k ≥ ρ` on, the sequence is `2^(-k)`-Cauchy on `B_ρ` after the cumulative index. -/
theorem IsLocL2Cauchy.eLpNorm_sub_le {D : ℕ → Vec d → ℝ} (hD : IsLocL2Cauchy D) {ρ : ℝ} {k : ℕ}
    (hk : ρ ≤ k) {p q : ℕ} (hp : cumCauchyIndex D k ≤ p) (hq : cumCauchyIndex D k ≤ q) :
    eLpNorm (fun x => D p x - D q x) 2 (volume.restrict (ball 0 ρ)) ≤ (2⁻¹ : ℝ≥0∞) ^ k :=
  (eLpNorm_mono_measure _ (Measure.restrict_mono (ball_subset_ball_of_le hk) le_rfl)).trans
    ((hD.cauchyAt_cauchyIndex k).mono (cauchyIndex_le_cumCauchyIndex D le_rfl) p q hp hq)

theorem tsum_two_inv_pow_ne_top (K : ℕ) : ∑' n : ℕ, 2 * (2⁻¹ : ℝ≥0∞) ^ (n + K) ≠ ⊤ := by
  rw [ENNReal.tsum_mul_left]
  refine ENNReal.mul_ne_top ENNReal.ofNat_ne_top ?_
  simp_rw [pow_add, ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
  refine ENNReal.mul_ne_top ?_ (ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr two_ne_zero))
  rw [ENNReal.one_sub_inv_two, inv_inv]
  exact ENNReal.ofNat_ne_top

/-- Along the cumulative indices the sequence converges almost everywhere on every ball. -/
theorem IsLocL2Cauchy.ae_tendsto {D : ℕ → Vec d → ℝ} (hD : IsLocL2Cauchy D)
    (hmeas : ∀ p, AEStronglyMeasurable (D p) volume) (ρ : ℝ) :
    ∀ᵐ x ∂(volume.restrict (ball (0 : Vec d) ρ)),
      Tendsto (fun k => D (cumCauchyIndex D k) x) atTop (𝓝 (locL2Limit D x)) := by
  obtain ⟨K, hK⟩ := exists_nat_ge ρ
  set E : ℕ → Vec d → ℝ := fun n => D (cumCauchyIndex D (n + K)) with hE
  have hcau : ∀ N n m : ℕ, N ≤ n → N ≤ m →
      eLpNorm (E n - E m) 2 (volume.restrict (ball (0 : Vec d) ρ)) <
        2 * (2⁻¹ : ℝ≥0∞) ^ (N + K) := by
    intro N n m hn hm
    have hle := hD.eLpNorm_sub_le (k := N + K) (hK.trans (by exact_mod_cast Nat.le_add_left K N))
      (cumCauchyIndex_mono D (by omega : N + K ≤ n + K))
      (cumCauchyIndex_mono D (by omega : N + K ≤ m + K))
    refine lt_of_le_of_lt hle ?_
    have hpos : (2⁻¹ : ℝ≥0∞) ^ (N + K) ≠ 0 :=
      pow_ne_zero _ (ENNReal.inv_ne_zero.mpr ENNReal.ofNat_ne_top)
    have hfin : (2⁻¹ : ℝ≥0∞) ^ (N + K) ≠ ⊤ :=
      ENNReal.pow_ne_top (ENNReal.inv_ne_top.mpr two_ne_zero)
    rw [two_mul]
    exact ENNReal.lt_add_right hfin hpos
  have hae := Lp.ae_tendsto_of_cauchy_eLpNorm (μ := volume.restrict (ball (0 : Vec d) ρ))
    (fun n => (hmeas _).restrict) (p := 2) (by norm_num) (tsum_two_inv_pow_ne_top K) hcau
  filter_upwards [hae] with x hx
  obtain ⟨l, hl⟩ := hx
  have hl' : Tendsto (fun k => D (cumCauchyIndex D k) x) atTop (𝓝 l) :=
    (tendsto_add_atTop_iff_nat K).mp hl
  rw [locL2Limit, hl'.limsup_eq]
  exact hl'

theorem measurable_locL2Limit {D : ℕ → Vec d → ℝ} (hmeas : ∀ p, Measurable (D p)) :
    Measurable (locL2Limit D) :=
  Measurable.limsup fun _ => hmeas _

/-- **`L²_loc` convergence to the selected limit.** -/
theorem IsLocL2Cauchy.tendsto_eLpNorm {D : ℕ → Vec d → ℝ} (hD : IsLocL2Cauchy D)
    (hmeas : ∀ p, Measurable (D p)) (ρ : ℝ) :
    Tendsto (fun p => eLpNorm (fun x => D p x - locL2Limit D x) 2
      (volume.restrict (ball 0 ρ))) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro δ hδ
  obtain ⟨K₀, hK₀⟩ := exists_nat_ge ρ
  have hgeo : Tendsto (fun k : ℕ => (2⁻¹ : ℝ≥0∞) ^ k) atTop (𝓝 0) :=
    ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (ENNReal.inv_lt_one.mpr (by norm_num))
  obtain ⟨K₁, hK₁⟩ := eventually_atTop.mp ((ENNReal.tendsto_nhds_zero.mp hgeo) δ hδ)
  set k := max K₀ K₁
  have hk : ρ ≤ k := hK₀.trans (by exact_mod_cast le_max_left K₀ K₁)
  refine eventually_atTop.mpr ⟨cumCauchyIndex D k, fun p hp => ?_⟩
  have hae := hD.ae_tendsto (fun q => (hmeas q).aestronglyMeasurable) ρ
  have hlim : ∀ᵐ x ∂(volume.restrict (ball (0 : Vec d) ρ)),
      Tendsto (fun n => D p x - D (cumCauchyIndex D n) x) atTop (𝓝 (D p x - locL2Limit D x)) :=
    hae.mono fun x hx => tendsto_const_nhds.sub hx
  have hfatou := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := 2)
    (f := fun n x => D p x - D (cumCauchyIndex D n) x)
    (fun n => ((hmeas p).sub (hmeas _)).aestronglyMeasurable)
    (fun x => D p x - locL2Limit D x)
    ((hmeas p).sub (measurable_locL2Limit hmeas)).aestronglyMeasurable hlim
  refine hfatou.trans ((liminf_le_of_frequently_le' (eventually_atTop.mpr ⟨k, fun n hn =>
    hD.eLpNorm_sub_le hk hp (cumCauchyIndex_mono D hn)⟩).frequently).trans ?_)
  exact hK₁ k (le_max_right _ _)

end EinsteinFull.Homogenization
