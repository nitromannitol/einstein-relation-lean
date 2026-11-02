import EinsteinFull.Calculus.ParabolicBridgeAssembly1
import EinsteinFull.Calculus.ParabolicBridgeParH1
import EinsteinFull.Calculus.ParabolicLibraryBridgeCore

/-!
# The scaled oscillation decay for the delayed mollification

For `MolData` on a cylinder, the mean oscillation of `V` on a smaller cylinder is bounded by the
`L²` norm of `V - κ` on a fixed library cylinder.
-/

open scoped ENNReal

noncomputable section
namespace EinsteinFull.ParabolicBridge

open MeasureTheory Set Filter Topology PDE

theorem toReal_le_of_le_ofReal' {t : ℝ≥0∞} {c : ℝ} (hc : 0 ≤ c) (ht : t ≤ ENNReal.ofReal c) :
    t.toReal ≤ c := by
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top ht
  rwa [ENNReal.toReal_ofReal hc] at this

theorem scaled_osc_bound (d : ℕ) (hd : 0 < d) (Lam : ℝ) (hLam : 1 ≤ Lam) :
    ∃ α C : ℝ, 0 < α ∧ α ≤ 1 ∧ 1 ≤ C ∧
    ∀ (x : Vec d) (r K : ℝ), 0 < r → 1 ≤ K →
    ∀ (A : Vec d → Mat d) (V : Vec d × ℝ → ℝ) (G : Fin d → Vec d × ℝ → ℝ),
    MolData (euclideanBall x r) (-r ^ 2 / K) 0 Lam A V G →
    ∀ (κ θ : ℝ), 0 < θ → 2 * Real.sqrt K * θ ≤ 3 / 8 →
      Real.sqrt (⨍ z, |V z - ⨍ w, V w ∂(volume.restrict
          (euclideanBall x (θ * r) ×ˢ Ioo (-(θ * r) ^ 2 / K) 0))| ^ 2
          ∂(volume.restrict (euclideanBall x (θ * r) ×ˢ Ioo (-(θ * r) ^ 2 / K) 0))) ≤
        C * (2 * Real.sqrt K * θ) ^ α / 2 *
          (((r / (2 * Real.sqrt K)) ^ (d + 2))⁻¹) ^ (1 / 2 : ℝ) *
          (eLpNorm (fun z => V z - κ) 2
            (volume.restrict (euclideanBall x (r / (2 * Real.sqrt K)) ×ˢ
              Ioc (0 - (r / (2 * Real.sqrt K)) ^ 2) 0))).toReal := by
  obtain ⟨α, C, hα0, hα1, hC1, hcore⟩ := parabolic_core d hd Lam hLam
  refine ⟨α, C, hα0, hα1, hC1, ?_⟩
  intro x r K hr hK A V G h κ θ hθ hθ'
  have hK0 : 0 < K := by linarith
  have hs : 0 < Real.sqrt K := Real.sqrt_pos.mpr hK0
  have hs1 : 1 ≤ Real.sqrt K := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hK
  have hss : Real.sqrt K * Real.sqrt K = K := Real.mul_self_sqrt hK0.le
  generalize Real.sqrt K = s at hs hs1 hss hθ' ⊢
  have hρ' : 0 < r / (2 * s) := by positivity
  have hρ'r : r / (2 * s) ≤ r := div_le_self hr.le (by linarith)
  have hθ'pos : 0 < 2 * s * θ := by positivity
  have hθρ : (2 * s * θ) * (r / (2 * s)) = θ * r := by field_simp
  have hθ1 : θ ≤ 1 := by nlinarith
  have hρ'2 : (r / (2 * s)) ^ 2 = r ^ 2 / (4 * K) := by
    rw [← hss]
    field_simp
    ring
  have hθr : θ * r ≤ r := by nlinarith
  have hθr0 : 0 < θ * r := mul_pos hθ hr
  have hθr2 : (θ * r) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hθr0.le hθr 2
  -- the cylinders
  have hEsub : euclideanBall x (θ * r) ×ˢ Ioo (-(θ * r) ^ 2 / K) 0 ⊆
      euclideanBall x r ×ˢ Ioo (-r ^ 2 / K) 0 := by
    refine Set.prod_mono (euclideanBall_mono hθr0.le hθr) (Set.Ioo_subset_Ioo_left ?_)
    rw [div_le_div_iff_of_pos_right hK0]
    linarith
  have hEsubR : euclideanBall x (θ * r) ×ˢ Ioo (-(θ * r) ^ 2 / K) 0 ⊆
      euclideanBall x (θ * r) ×ˢ Ioc (0 - (θ * r) ^ 2) 0 := by
    intro z hz
    refine ⟨hz.1, ?_, hz.2.2.le⟩
    have h1 : -(θ * r) ^ 2 ≤ -(θ * r) ^ 2 / K := by
      rw [neg_div]
      have : (θ * r) ^ 2 / K ≤ (θ * r) ^ 2 := div_le_self (sq_nonneg _) hK
      linarith
    linarith [hz.2.1]
  have hSm : MeasurableSet (euclideanBall x r ×ˢ Ioo (-r ^ 2 / K) 0) := h.measurableSet_S
  have hEm : MeasurableSet (euclideanBall x (θ * r) ×ˢ Ioo (-(θ * r) ^ 2 / K) 0) :=
    (isOpen_euclideanBall x _).measurableSet.prod measurableSet_Ioo
  have hEfin : volume (euclideanBall x (θ * r) ×ˢ Ioo (-(θ * r) ^ 2 / K) 0) ≠ ⊤ :=
    ne_top_of_le_ne_top h.vol_S.ne (measure_mono hEsub)
  haveI : IsFiniteMeasure
      (volume.restrict (euclideanBall x (θ * r) ×ˢ Ioo (-(θ * r) ^ 2 / K) 0)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hEfin⟩
  have hEpos : volume (euclideanBall x (θ * r) ×ˢ Ioo (-(θ * r) ^ 2 / K) 0) ≠ 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    refine (ENNReal.mul_pos (volume_euclideanBall_pos x hθr0).ne' ?_).ne'
    rw [Real.volume_Ioo]
    refine (ENNReal.ofReal_pos.mpr ?_).ne'
    have h2 : 0 < (θ * r) ^ 2 / K := by positivity
    have h3 : (0 : ℝ) - -(θ * r) ^ 2 / K = (θ * r) ^ 2 / K := by ring
    rw [h3]
    exact h2
  have hvolE : 0 < (volume.restrict
      (euclideanBall x (θ * r) ×ˢ Ioo (-(θ * r) ^ 2 / K) 0)).real Set.univ := by
    rw [measureReal_def, Measure.restrict_apply_univ]
    exact ENNReal.toReal_pos hEpos hEfin
  -- the extension by zero
  have hVx_m : Measurable ((euclideanBall x r ×ˢ Ioo (-r ^ 2 / K) 0).indicator V) :=
    h.measV.indicator hSm
  have hVx_2 : MemLp ((euclideanBall x r ×ˢ Ioo (-r ^ 2 / K) 0).indicator V) 2 volume :=
    indicator_memLp hSm h.memV
  have hVxl := (eLpNorm_two_lt_top_iff hVx_m.aestronglyMeasurable).mp hVx_2
  generalize hVx : (euclideanBall x r ×ˢ Ioo (-r ^ 2 / K) 0).indicator V = Vx at hVx_m hVx_2 hVxl
  -- constants
  generalize ha0 : ((volume.restrict
      (euclideanBall x (θ * r) ×ˢ Ioo (-(θ * r) ^ 2 / K) 0)).real Set.univ) ^ (-(1 / 2 : ℝ)) = a0
  generalize hb0 : C * (2 * s * θ) ^ α / 2 * (((r / (2 * s)) ^ (d + 2))⁻¹) ^ (1 / 2 : ℝ) = b0
  have ha0nn : 0 ≤ a0 := by rw [← ha0]; exact Real.rpow_nonneg hvolE.le _
  have hb0nn : 0 ≤ b0 := by
    rw [← hb0]
    have : 0 ≤ C := by linarith
    positivity
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hηpos : 0 < δ / (a0 + b0 + 1) := by positivity
  obtain ⟨ε₀, hε₀, hconv⟩ := MolS_L2_converges Vx hVx_m hVxl hηpos
  have hε : 0 < min (ε₀ / 2) (r ^ 2 / (8 * K)) := lt_min (by positivity) (by positivity)
  generalize hεdef : min (ε₀ / 2) (r ^ 2 / (8 * K)) = ε at hε
  have hεε₀ : ε < ε₀ := by
    rw [← hεdef]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hεr : ε ≤ r ^ 2 / (8 * K) := by rw [← hεdef]; exact min_le_right _ _
  have hD := hconv ε hε hεε₀
  obtain ⟨u, hu_fun, hu_grad, hu_sol⟩ := h.exists_solution hε
  have hufun : ∀ z, u.toFun z = MolS ε hε Vx z := by
    intro z
    rw [hu_fun z, hVx]
  -- restriction to the library cylinder
  have hU' : euclideanBall x (r / (2 * s)) ⊆ euclideanBall x r :=
    euclideanBall_mono hρ'.le hρ'r
  have hI' : Ioc (0 - (r / (2 * s)) ^ 2) 0 ⊆ Ioc (-r ^ 2 / K + 3 * ε) 0 := by
    refine Set.Ioc_subset_Ioc_left ?_
    rw [hρ'2]
    have hq : 0 ≤ r ^ 2 / K := by positivity
    have e1 : -r ^ 2 / K + 3 * (r ^ 2 / (8 * K)) - (0 - r ^ 2 / (4 * K)) =
        -(3 / 8) * (r ^ 2 / K) := by
      field_simp
      ring
    linarith
  have hsol' := PDE.Parabolic.NashLower.isParabolicWeakSolution_restrict hU' hI' hu_sol
  have hcoef := PDE.Parabolic.NashLower.isParabolicCoeff_mono
    (h.isParabolicCoeff (Ioc (-r ^ 2 / K + 3 * ε) 0)) hU' hI'
  obtain ⟨m', M', hbd, hgap⟩ := hcore (fun z : Vec d × ℝ => A z.1) x 0 (r / (2 * s)) hρ' hcoef
    (PDE.Parabolic.NashLower.restrictParH1 hU' hI' u) hsol' κ (2 * s * θ) hθ'pos hθ'
  rw [hθρ] at hbd
  set E : Set (Vec d × ℝ) := euclideanBall x (θ * r) ×ˢ Ioo (-(θ * r) ^ 2 / K) 0 with hE
  set Q : Set (Vec d × ℝ) :=
    euclideanBall x (r / (2 * s)) ×ˢ Ioc (0 - (r / (2 * s)) ^ 2) 0 with hQ
  have e' : ∀ z, (PDE.Parabolic.NashLower.restrictParH1 hU' hI' u).toFun z =
      MolS ε hε Vx z := fun z => hufun z
  have hbdE : ∀ᵐ z ∂(volume.restrict E), m' ≤ MolS ε hε Vx z ∧ MolS ε hε Vx z ≤ M' := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hEsubR hbd] with z hz
    rwa [e' z] at hz
  have hMS2 : MemLp (MolS ε hε Vx) 2 volume := (eLpNorm_MolS_le Vx hVx_m).trans_lt hVx_2
  have hVE : MemLp V 2 (volume.restrict E) :=
    h.memV.mono_measure (Measure.restrict_mono hEsub le_rfl)
  have R1 := sqrt_avg_osc_le (volume.restrict E) hvolE hVE (hMS2.restrict E) hbdE
  rw [ha0] at R1
  have hMSne : eLpNorm (MolS ε hε Vx - Vx) 2 volume ≠ ⊤ := (hMS2.sub hVx_2).ne
  have hT2 : (eLpNorm (MolS ε hε Vx - Vx) 2 volume).toReal ≤ δ / (a0 + b0 + 1) :=
    toReal_le_of_le_ofReal' hηpos.le hD
  have hT1 : (eLpNorm (V - MolS ε hε Vx) 2 (volume.restrict E)).toReal ≤ δ / (a0 + b0 + 1) := by
    have h1 : eLpNorm (V - MolS ε hε Vx) 2 (volume.restrict E) =
        eLpNorm (Vx - MolS ε hε Vx) 2 (volume.restrict E) := by
      refine eLpNorm_congr_ae ?_
      filter_upwards [ae_restrict_mem hEm] with z hz
      have hz' : Vx z = V z := by rw [← hVx]; exact Set.indicator_of_mem (hEsub hz) V
      simp only [Pi.sub_apply, hz']
    have h2 : eLpNorm (Vx - MolS ε hε Vx) 2 (volume.restrict E) ≤
        eLpNorm (MolS ε hε Vx - Vx) 2 volume := by
      rw [eLpNorm_sub_comm]
      exact eLpNorm_mono_measure _ Measure.restrict_le_self
    rw [h1]
    exact (ENNReal.toReal_mono hMSne h2).trans hT2
  have hbQ : -r ^ 2 / K ≤ 0 - (r / (2 * s)) ^ 2 := by
    rw [hρ'2]
    have e2 : r ^ 2 / (4 * K) ≤ r ^ 2 / K :=
      div_le_div_of_nonneg_left (sq_nonneg r) hK0 (by linarith)
    have e3 : -r ^ 2 / K = -(r ^ 2 / K) := by ring
    linarith
  have hQfin : volume Q ≠ ⊤ := by
    rw [hQ, Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_ne_top (volume_euclideanBall_ne_top x hρ'.le) (by simp [Real.volume_Ioc])
  haveI : IsFiniteMeasure (volume.restrict Q) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hQfin⟩
  have hae : ∀ᵐ z ∂(volume.restrict Q), Vx z = V z := by
    filter_upwards [ae_indicator_eq_on_Ioc hU' (isOpen_euclideanBall x _).measurableSet hbQ V]
      with z hz
    rw [← hVx]
    exact hz
  have hVQ : MemLp (fun z => V z - κ) 2 (volume.restrict Q) := by
    have h1 : MemLp (fun z => Vx z - κ) 2 (volume.restrict Q) :=
      (hVx_2.restrict Q).sub (memLp_const κ)
    refine h1.ae_eq ?_
    filter_upwards [hae] with z hz
    simp only [hz]
  have hQ1 : eLpNorm (fun z => MolS ε hε Vx z - κ) 2 (volume.restrict Q) ≤
      eLpNorm (MolS ε hε Vx - Vx) 2 volume +
        eLpNorm (fun z => V z - κ) 2 (volume.restrict Q) := by
    have e1 : (fun z => MolS ε hε Vx z - κ) = (MolS ε hε Vx - Vx) + (fun z => Vx z - κ) := by
      funext z
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    rw [e1]
    refine (eLpNorm_add_le (by norm_num)).trans
      (add_le_add (eLpNorm_mono_measure _ Measure.restrict_le_self) (le_of_eq ?_))
    refine eLpNorm_congr_ae ?_
    filter_upwards [hae] with z hz
    simp only [hz]
  have hQ2 : (eLpNorm (fun z => MolS ε hε Vx z - κ) 2 (volume.restrict Q)).toReal ≤
      δ / (a0 + b0 + 1) + (eLpNorm (fun z => V z - κ) 2 (volume.restrict Q)).toReal := by
    calc (eLpNorm (fun z => MolS ε hε Vx z - κ) 2 (volume.restrict Q)).toReal
        ≤ (eLpNorm (MolS ε hε Vx - Vx) 2 volume +
            eLpNorm (fun z => V z - κ) 2 (volume.restrict Q)).toReal :=
          ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hMSne, hVQ.ne⟩) hQ1
      _ = (eLpNorm (MolS ε hε Vx - Vx) 2 volume).toReal +
            (eLpNorm (fun z => V z - κ) 2 (volume.restrict Q)).toReal :=
          ENNReal.toReal_add hMSne hVQ.ne
      _ ≤ _ := add_le_add hT2 le_rfl
  have efun : (fun z => (PDE.Parabolic.NashLower.restrictParH1 hU' hI' u).toFun z - κ) =
      fun z => MolS ε hε Vx z - κ := funext fun z => by rw [e' z]
  have hmeasQ : AEStronglyMeasurable
      (fun z => (PDE.Parabolic.NashLower.restrictParH1 hU' hI' u).toFun z - κ)
      (volume.restrict Q) := by
    rw [efun]
    exact ((MolS_measurable Vx hVx_m).sub measurable_const).aestronglyMeasurable
  have hcn := core_norm_eq (volume.restrict Q) (((r / (2 * s)) ^ (d + 2))⁻¹) (by positivity)
    (fun z => (PDE.Parabolic.NashLower.restrictParH1 hU' hI' u).toFun z - κ) hmeasQ
  rw [hcn, efun] at hgap
  have hηeq : δ / (a0 + b0 + 1) * (a0 + b0 + 1) = δ := by
    field_simp
  have hgap2 : (M' - m') / 2 ≤ b0 * (δ / (a0 + b0 + 1) +
      (eLpNorm (fun z => V z - κ) 2 (volume.restrict Q)).toReal) := by
    calc (M' - m') / 2 ≤ (C * (2 * s * θ) ^ α * ((((r / (2 * s)) ^ (d + 2))⁻¹) ^ (1 / 2 : ℝ) *
          (eLpNorm (fun z => MolS ε hε Vx z - κ) 2 (volume.restrict Q)).toReal)) / 2 := by
          linarith
      _ = b0 * (eLpNorm (fun z => MolS ε hε Vx z - κ) 2 (volume.restrict Q)).toReal := by
          rw [← hb0]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hQ2 hb0nn
  have hfin := le_trans R1 (add_le_add (mul_le_mul_of_nonneg_left hT1 ha0nn) hgap2)
  nlinarith [hfin, hηeq, hηpos]

end EinsteinFull.ParabolicBridge
