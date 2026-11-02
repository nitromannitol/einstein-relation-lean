import EinsteinRelation.Entropy.LocalTestApproximation
import EinsteinRelation.Correctors.CanonicalFluxDivergenceSupport
import EinsteinRelation.Calculus.HorizontalWeakL1UniquenessSupport
import EinsteinRelation.Entropy.DivergenceBoundNoChain
import EinsteinRelation.Entropy.ResolventFromWeak

/-! # Lemma 4.2, second assertion

Source: `paper/main.tex` 619-638 (`entropy.divergence`). This file proves the second assertion
`E[ρ_s D·F] = -E[Dρ_s · F]` by smoothing the density `ρ_s` instead of the field `F`.

* The weak divergence `h` of a field `F` that is local in `B_r` is local in every larger ball, up
  to a null set (`exists_local_ae_eq_of_hasWeakHorizontalDivergence`). The horizontal smoothing
  `S_ε h` equals `-∑ᵢ (∂ᵢζ_ε) ⋆ Fᵢ` almost surely, which is local in `B_{r+ε}`.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

namespace EinsteinRelation.Entropy

variable {d : ℕ}

/-! ## Integrability of horizontal smoothings -/

theorem integrable_comp_translate' {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {u : FieldPair d → ℝ} (hu : Integrable u Q) (y : Vec d) :
    Integrable (fun ω => u (translate y ω)) Q := by
  have h : Integrable u (Measure.map (translate y) Q) := by
    rw [hQ y]
    exact hu
  exact h.comp_measurable (Probability.measurable_translate y)

theorem integrable_prod_kernel_translate {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {κ : Vec d → ℝ} (hκm : Measurable κ) (hκi : Integrable κ)
    {u : FieldPair d → ℝ} (hum : Measurable u) (hui : Integrable u Q) :
    Integrable (fun p : FieldPair d × Vec d => κ p.2 * u (translate p.2 p.1)) (Q.prod volume) := by
  have hmeas : Measurable (fun p : FieldPair d × Vec d => κ p.2 * u (translate p.2 p.1)) :=
    (hκm.comp measurable_snd).mul (hum.comp
      (Probability.continuous_translate.measurable.comp (measurable_snd.prodMk measurable_fst)))
  rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun y => ?_, ?_⟩
  · exact (integrable_comp_translate' hQ hui y).const_mul (κ y)
  · have hnorm : ∀ y : Vec d, (∫ ω, ‖κ y * u (translate y ω)‖ ∂Q) =
        ‖κ y‖ * ∫ ω, ‖u ω‖ ∂Q := by
      intro y
      have h1 : (fun ω => ‖κ y * u (translate y ω)‖) = fun ω => ‖κ y‖ * ‖u (translate y ω)‖ := by
        funext ω
        rw [norm_mul]
      rw [h1, integral_const_mul]
      congr 1
      exact Probability.integral_translate Q hQ y (fun η => ‖u η‖) hum.norm
    refine Integrable.congr (hκi.norm.mul_const (∫ ω, ‖u ω‖ ∂Q))
      (Filter.Eventually.of_forall fun y => ?_)
    exact (hnorm y).symm

theorem integrable_horizontalMollify' {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {κ : Vec d → ℝ} (hκm : Measurable κ) (hκi : Integrable κ)
    {u : FieldPair d → ℝ} (hum : Measurable u) (hui : Integrable u Q) :
    Integrable (horizontalMollify κ u) Q :=
  (integrable_prod_kernel_translate hQ hκm hκi hum hui).integral_prod_left

/-- The weak divergence identity, tested against an orbit-core test. -/
theorem HasWeakHorizontalDivergence.integral_test {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] {hQ : IsStationary Q} {V : FieldPair d → Vec d}
    {h : FieldPair d → ℝ} (hV : HasWeakHorizontalDivergence Q hQ V h) {G : FieldPair d → ℝ}
    (hG : IsHorizontalTest G) :
    ∫ ω, (∑ i, V ω i * horizontalDerivative i G ω) ∂Q = -∫ ω, h ω * G ω ∂Q := by
  have key := hV.2.2 ((hG.memLp Q 2).toLp G) (hG.isHorizontallySmoothTest Q hQ)
    (fun i => (hG.memLp_derivative Q 2 i).toLp (horizontalDerivative i G))
    (fun i => hG.hasHorizontalLpDerivative_toLp Q hQ i)
  have e1 : ∫ ω, (∑ i, V ω i * ((hG.memLp_derivative Q 2 i).toLp (horizontalDerivative i G)) ω) ∂Q
      = ∫ ω, (∑ i, V ω i * horizontalDerivative i G ω) ∂Q := by
    refine integral_congr_ae ?_
    filter_upwards [ae_all_iff.mpr fun i => (hG.memLp_derivative Q 2 i).coeFn_toLp] with ω hω
    simp only [hω]
  have e2 : ∫ ω, h ω * ((hG.memLp Q 2).toLp G) ω ∂Q = ∫ ω, h ω * G ω ∂Q := by
    refine integral_congr_ae ?_
    filter_upwards [(hG.memLp Q 2).coeFn_toLp] with ω hω
    simp only [hω]
  rw [← e1, ← e2]
  exact key

/-! ## The smoothed divergence -/

/-- The reflected kernel `ζ(-·)`. -/
def reflectKernel (ζ : Vec d → ℝ) : Vec d → ℝ := fun x => ζ (-x)

/-- The kernel of the `i`-th divergence term, `y ↦ ∂ᵢ(ζ(-·))(-y)`. -/
def divKernel (ζ : Vec d → ℝ) (i : Fin d) : Vec d → ℝ :=
  fun y => coordinateDerivative i (reflectKernel ζ) (-y)

theorem contDiff_reflectKernel {ζ : Vec d → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) :
    ContDiff ℝ (⊤ : ℕ∞) (reflectKernel ζ) :=
  hζ.comp contDiff_neg

theorem hasCompactSupport_reflectKernel {ζ : Vec d → ℝ} (hζc : HasCompactSupport ζ) :
    HasCompactSupport (reflectKernel ζ) :=
  hζc.comp_homeomorph (Homeomorph.neg (Vec d))

theorem continuous_divKernel {ζ : Vec d → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (i : Fin d) :
    Continuous (divKernel ζ i) := by
  have h1 : Continuous fun x => fderiv ℝ (reflectKernel ζ) x :=
    (contDiff_reflectKernel hζ).continuous_fderiv (by simp)
  exact (h1.clm_apply continuous_const).comp continuous_neg

theorem hasCompactSupport_divKernel {ζ : Vec d → ℝ} (hζc : HasCompactSupport ζ) (i : Fin d) :
    HasCompactSupport (divKernel ζ i) := by
  have h1 : HasCompactSupport (fun x => fderiv ℝ (reflectKernel ζ) x (unitVector i)) :=
    (hasCompactSupport_reflectKernel hζc).fderiv_apply (𝕜 := ℝ) (unitVector i)
  exact h1.comp_homeomorph (Homeomorph.neg (Vec d))

/-- **The smoothed weak divergence.** For a field `V` with weak divergence `h`, the horizontal
smoothing of `h` by `ζ` is `∑ᵢ (divKernel ζ i) ⋆ Vᵢ` almost surely. -/
theorem ae_horizontalMollify_eq_of_hasWeakHorizontalDivergence {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) {ζ : Vec d → ℝ}
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hζc : HasCompactSupport ζ) {V : FieldPair d → Vec d}
    {h : FieldPair d → ℝ} (hVm : Measurable V) (hVi : ∀ i, Integrable (fun ω => V ω i) Q)
    (hhm : Measurable h) (hhi : Integrable h Q) (hdiv : HasWeakHorizontalDivergence Q hQ V h) :
    horizontalMollify ζ h =ᵐ[Q]
      fun ω => ∑ i, horizontalMollify (divKernel ζ i) (fun ω => V ω i) ω := by
  have hζm : Measurable ζ := hζ.continuous.measurable
  have hζi : Integrable ζ := hζ.continuous.integrable_of_hasCompactSupport hζc
  have hκm : ∀ i, Measurable (divKernel ζ i) := fun i => (continuous_divKernel hζ i).measurable
  have hκi : ∀ i, Integrable (divKernel ζ i) := fun i =>
    (continuous_divKernel hζ i).integrable_of_hasCompactSupport (hasCompactSupport_divKernel hζc i)
  have hVim : ∀ i, Measurable fun ω => V ω i := fun i => (measurable_pi_apply i).comp hVm
  have hSh := integrable_horizontalMollify' hQ hζm hζi hhm hhi
  have hSV : ∀ i, Integrable (horizontalMollify (divKernel ζ i) (fun ω => V ω i)) Q := fun i =>
    integrable_horizontalMollify' hQ (hκm i) (hκi i) (hVim i) (hVi i)
  set g : FieldPair d → ℝ := fun ω => horizontalMollify ζ h ω -
    ∑ i, horizontalMollify (divKernel ζ i) (fun ω => V ω i) ω with hgdef
  have hgi : Integrable g Q := hSh.sub (integrable_finset_sum _ fun i _ => hSV i)
  have hpair : ∀ H : FieldPair d → ℝ, IsHorizontalTest H → ∫ ω, g ω * H ω ∂Q = 0 := by
    intro H hH
    obtain ⟨B, -, hB⟩ := hH.bound_orbit
    have hHB : ∀ ω, |H ω| ≤ B := fun ω => by simpa using hB ω 0
    have hHBae : ∀ᵐ ω ∂Q, ‖H ω‖ ≤ B := ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]; exact hHB ω
    set G := horizontalMollify (reflectKernel ζ) H with hGdef
    have hG : IsHorizontalTest G := Correctors.isHorizontalTest_horizontalMollify _
      (contDiff_reflectKernel hζ) (hasCompactSupport_reflectKernel hζc) H hH.1 ⟨B, hHB⟩
    have hrefl : ∀ ω, (∫ y, ζ y * H (translate (-y) ω)) = G ω := fun ω => by
      have e := integral_neg_eq_self (fun x : Vec d => ζ (-x) * H (translate x ω))
        (volume : Measure (Vec d))
      simp only [neg_neg] at e
      rw [e]
      rfl
    have hDG : ∀ i ω, horizontalDerivative i G ω =
        -∫ y, divKernel ζ i y * H (translate (-y) ω) := by
      intro i ω
      rw [Correctors.horizontalMollify_horizontalDerivative_formula (contDiff_reflectKernel hζ)
        (hasCompactSupport_reflectKernel hζc) hH.1 ⟨B, hHB⟩ i ω]
      congr 1
      exact (integral_neg_eq_self
        (fun x : Vec d => coordinateDerivative i (reflectKernel ζ) x * H (translate x ω))
        (volume : Measure (Vec d))).symm
    have hA : ∫ ω, horizontalMollify ζ h ω * H ω ∂Q = ∫ ω, h ω * G ω ∂Q := by
      rw [Calculus.integral_horizontalMollify_mul_eq_adj hQ hζm hζi hhm hhi hH.1 hHB]
      exact integral_congr_ae (ae_of_all _ fun ω => by simp only [hrefl ω])
    have hB' : ∀ i, ∫ ω, horizontalMollify (divKernel ζ i) (fun ω => V ω i) ω * H ω ∂Q =
        -∫ ω, V ω i * horizontalDerivative i G ω ∂Q := by
      intro i
      rw [Calculus.integral_horizontalMollify_mul_eq_adj hQ (hκm i) (hκi i) (hVim i) (hVi i) hH.1
        hHB, ← integral_neg]
      exact integral_congr_ae (ae_of_all _ fun ω => by simp only [hDG i ω, mul_neg, neg_neg])
    have hVD : ∀ i, Integrable (fun ω => V ω i * horizontalDerivative i G ω) Q := by
      intro i
      obtain ⟨Bi, -, hBi⟩ := hG.bound_derivative i
      exact (hVi i).mul_bdd (hG.measurable_derivative i).aestronglyMeasurable
        (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hBi ω 0)
    have hsum : ∫ ω, (∑ i, V ω i * horizontalDerivative i G ω) ∂Q =
        ∑ i, ∫ ω, V ω i * horizontalDerivative i G ω ∂Q :=
      integral_finset_sum _ fun i _ => hVD i
    have hW := HasWeakHorizontalDivergence.integral_test hdiv hG
    have hI1 : Integrable (fun ω => horizontalMollify ζ h ω * H ω) Q := hSh.mul_bdd hH.1.aestronglyMeasurable hHBae
    have hI2 : ∀ i, Integrable (fun ω => horizontalMollify (divKernel ζ i) (fun ω => V ω i) ω * H ω) Q :=
      fun i => (hSV i).mul_bdd hH.1.aestronglyMeasurable hHBae
    have e : (fun ω => g ω * H ω) = fun ω => horizontalMollify ζ h ω * H ω -
        ∑ i, horizontalMollify (divKernel ζ i) (fun ω => V ω i) ω * H ω := by
      funext ω
      simp only [hgdef, sub_mul, Finset.sum_mul]
    rw [e, integral_sub hI1 (integrable_finset_sum _ fun i _ => hI2 i),
      integral_finset_sum _ fun i _ => hI2 i, hA, Finset.sum_congr rfl fun i _ => hB' i,
      Finset.sum_neg_distrib, ← hsum, hW]
    ring
  have hzero := eq_zero_of_horizontalCore_pairing_eq_zero_l1 Q hQ (hgi.toL1 g)
    fun H hH => by
      rw [← hpair H hH]
      exact integral_congr_ae ((hgi.coeFn_toL1).mono fun ω hω => by simp only [hω])
  have hg0 : g =ᵐ[Q] 0 := by
    have h1 := hgi.coeFn_toL1
    rw [hzero] at h1
    exact h1.symm.trans (Lp.coeFn_zero ℝ 1 Q)
  filter_upwards [hg0] with ω hω
  simp only [hgdef, Pi.zero_apply, sub_eq_zero] at hω
  exact hω

/-! ## Locality of the weak divergence -/

theorem euclideanNorm_neg' (z : Vec d) : euclideanNorm (-z) = euclideanNorm z := by
  have h := TimeChange.euclideanNorm_smul (-1) z
  rwa [neg_one_smul, abs_neg, abs_one, one_mul] at h

/-- The divergence kernel of the rescaled mollifier vanishes outside the closed ball of radius
`ε`. -/
theorem divKernel_eq_zero_of_lt {ε : ℝ} (hε : 0 < ε) (i : Fin d) {y : Vec d}
    (hy : ε < euclideanNorm y) : divKernel (Calculus.unitMassScaledMollifier d ε) i y = 0 := by
  have hsub : tsupport (reflectKernel (Calculus.unitMassScaledMollifier d ε)) ⊆
      {z : Vec d | euclideanNorm z ≤ ε} := by
    refine closure_minimal (fun z hz => ?_)
      (isClosed_le continuous_euclideanNorm' continuous_const)
    have hz' : Calculus.unitMassScaledMollifier d ε (-z) ≠ 0 := hz
    have h1 := euclideanNorm_lt_of_unitMassScaledMollifier_ne_zero hε hz'
    rw [euclideanNorm_neg'] at h1
    exact h1.le
  have hnot : -y ∉ tsupport (reflectKernel (Calculus.unitMassScaledMollifier d ε)) := by
    intro hmem
    have h1 : euclideanNorm (-y) ≤ ε := hsub hmem
    rw [euclideanNorm_neg'] at h1
    linarith
  show fderiv ℝ (reflectKernel (Calculus.unitMassScaledMollifier d ε)) (-y) (unitVector i) = 0
  rw [fderiv_of_notMem_tsupport ℝ hnot]
  simp

/-- Smoothing by a divergence kernel of a field local in `B_r` is local in `B_{r+ε}`. -/
theorem measurable_localSigma_horizontalMollify_divKernel {r ε : ℝ} (hε : 0 < ε) (i : Fin d)
    {u : FieldPair d → ℝ} (hu : Measurable[localSigma {y : Vec d | euclideanNorm y < r}] u) :
    Measurable[localSigma {y : Vec d | euclideanNorm y < r + ε}]
      (horizontalMollify (divKernel (Calculus.unitMassScaledMollifier d ε) i) u) := by
  set S : Set (Vec d) := {z | euclideanNorm z ≤ ε} with hSdef
  have hS : MeasurableSet S := measurableSet_le continuous_euclideanNorm'.measurable measurable_const
  have heq : horizontalMollify (divKernel (Calculus.unitMassScaledMollifier d ε) i) u =
      fun w => ∫ z in S, divKernel (Calculus.unitMassScaledMollifier d ε) i z * u (translate z w) := by
    funext w
    unfold horizontalMollify
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_).symm
    have hz' : ε < euclideanNorm z := by
      simp only [hSdef, Set.mem_setOf_eq, not_le] at hz
      exact hz
    rw [divKernel_eq_zero_of_lt hε i hz', zero_mul]
  rw [heq]
  refine measurable_localSigma_setIntegral_translate hS (fun x hx y hy => ?_) _
    (continuous_divKernel (contDiff_unitMassScaledMollifier ε) i).measurable u hu
  have h := TimeChange.euclideanNorm_add_le x y
  simp only [hSdef, Set.mem_setOf_eq] at hx hy ⊢
  linarith

/-- **Locality of the weak divergence.** The weak divergence `h ∈ L^q` of a field local in `B_r`
agrees almost surely with a function local in `B_{r'}`, for every `r' > r`. -/
theorem exists_local_ae_eq_of_hasWeakHorizontalDivergence {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) {r r' : ℝ} (hrr : r < r') {q : ℝ≥0∞}
    [Fact (1 ≤ q)] (hq : q ≠ ⊤) {V : FieldPair d → Vec d} {h : FieldPair d → ℝ}
    (hVl : Measurable[localSigma {y : Vec d | euclideanNorm y < r}] V)
    (hVi : ∀ i, Integrable (fun ω => V ω i) Q) (hhm : Measurable h) (hhq : MemLp h q Q)
    (hdiv : HasWeakHorizontalDivergence Q hQ V h) :
    ∃ g : FieldPair d → ℝ, Measurable[localSigma {y : Vec d | euclideanNorm y < r'}] g ∧
      h =ᵐ[Q] g := by
  have hVm : Measurable V := hVl.mono (Probability.localSigma_le_borel _) le_rfl
  have hq1 : (1 : ℝ≥0∞) ≤ q := Fact.out
  have hhi : Integrable h Q := hhq.integrable hq1
  set δ := min (r' - r) 1 with hδdef
  have hδ : 0 < δ := lt_min (by linarith) one_pos
  have hconv := Calculus.tendsto_eLpNorm_horizontalMollify_unitMassScaledMollifier Q hQ q hq hhm hhq
  have hTM : TendstoInMeasure Q
      (fun ε => horizontalMollify (Calculus.unitMassScaledMollifier d ε) h) (𝓝[>] 0) h :=
    tendstoInMeasure_of_tendsto_eLpNorm (zero_lt_one.trans_le hq1).ne'
      hconv
  obtain ⟨ns, hns, hae⟩ := hTM.exists_seq_tendsto_ae'
  have hev : ∀ᶠ i in atTop, ns i ∈ Set.Ioo 0 δ := hns (Ioo_mem_nhdsGT hδ)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  set m : ℕ → ℝ := fun i => ns (i + N) with hmdef
  have hm : ∀ i, m i ∈ Set.Ioo 0 δ := fun i => hN (i + N) (Nat.le_add_left N i)
  set K : ℕ → FieldPair d → ℝ := fun i ω => ∑ j, horizontalMollify
    (divKernel (Calculus.unitMassScaledMollifier d (m i)) j) (fun ω => V ω j) ω with hKdef
  have hKl : ∀ i, Measurable[localSigma {y : Vec d | euclideanNorm y < r'}] (K i) := by
    intro i
    have hsub : {y : Vec d | euclideanNorm y < r + m i} ⊆ {y : Vec d | euclideanNorm y < r'} :=
      fun y hy => by
        simp only [Set.mem_setOf_eq] at hy ⊢
        have : m i < r' - r := lt_of_lt_of_le (hm i).2 (min_le_left _ _)
        linarith
    letI : MeasurableSpace (FieldPair d) := localSigma {y : Vec d | euclideanNorm y < r'}
    exact Finset.measurable_sum _ fun j _ =>
      (measurable_localSigma_horizontalMollify_divKernel (hm i).1 j
        ((measurable_pi_apply j).comp hVl)).mono (Probability.localSigma_mono hsub) le_rfl
  have hSK : ∀ᵐ ω ∂Q, ∀ i,
      horizontalMollify (Calculus.unitMassScaledMollifier d (m i)) h ω = K i ω :=
    ae_all_iff.mpr fun i => ae_horizontalMollify_eq_of_hasWeakHorizontalDivergence hQ
      (contDiff_unitMassScaledMollifier (m i)) (hasCompactSupport_unitMassScaledMollifier (hm i).1)
      hVm hVi hhm hhi hdiv
  refine ⟨fun ω => limsup (fun i => K i ω) atTop, ?_, ?_⟩
  · letI : MeasurableSpace (FieldPair d) := localSigma {y : Vec d | euclideanNorm y < r'}
    exact Measurable.limsup hKl
  · filter_upwards [hae, hSK] with ω hω hω'
    have h1 : Tendsto (fun i => K i ω) atTop (𝓝 (h ω)) :=
      ((tendsto_add_atTop_iff_nat N).mpr hω).congr fun i => hω' i
    exact h1.limsup_eq.symm

/-! ## Pairings in `L²` -/

theorem tendsto_zero_of_ofReal_abs_le' {x : ℕ → ℝ} {e : ℕ → ℝ≥0∞}
    (he : Tendsto e atTop (𝓝 0)) (hx : ∀ n, ENNReal.ofReal |x n| ≤ e n) :
    Tendsto x atTop (𝓝 0) := by
  have h1 : Tendsto (fun n => ENNReal.ofReal |x n|) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds he (fun n => zero_le) hx
  have h2 : Tendsto (fun n => (ENNReal.ofReal |x n|).toReal) atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    rw [ENNReal.toReal_zero] at h
    exact h
  have h3 : Tendsto (fun n => |x n|) atTop (𝓝 0) :=
    h2.congr fun n => ENNReal.toReal_ofReal (abs_nonneg _)
  exact (tendsto_zero_iff_abs_tendsto_zero x).mpr h3

/-- Pairings with a fixed `L²` function are continuous along `L²` convergence. -/
theorem tendsto_integral_mul_of_eLpNorm_two {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {f : Ω → ℝ} {g : ℕ → Ω → ℝ} {g0 : Ω → ℝ} (hf : MemLp f 2 μ) (hg : ∀ n, MemLp (g n) 2 μ)
    (hg0 : MemLp g0 2 μ)
    (hc : Tendsto (fun n => eLpNorm (fun w => g n w - g0 w) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ w, f w * g n w ∂μ) atTop (𝓝 (∫ w, f w * g0 w ∂μ)) := by
  have hdiff : ∀ n, ∫ w, f w * g n w ∂μ - ∫ w, f w * g0 w ∂μ =
      ∫ w, f w * (g n w - g0 w) ∂μ := fun n => by
    have hi1 : Integrable (fun w => f w * g n w) μ := hf.integrable_mul (hg n)
    have hi2 : Integrable (fun w => f w * g0 w) μ := hf.integrable_mul hg0
    rw [← integral_sub hi1 hi2]
    congr 1
    funext w
    ring
  have hT : Tendsto (fun n => ∫ w, f w * (g n w - g0 w) ∂μ) atTop (𝓝 0) := by
    refine tendsto_zero_of_ofReal_abs_le'
      (e := fun n => eLpNorm f 2 μ * eLpNorm (fun w => g n w - g0 w) 2 μ) ?_ fun n => ?_
    · have h := ENNReal.Tendsto.const_mul hc (Or.inr hf.eLpNorm_ne_top)
      rwa [mul_zero] at h
    · calc ENNReal.ofReal |∫ w, f w * (g n w - g0 w) ∂μ| = ‖∫ w, f w * (g n w - g0 w) ∂μ‖ₑ :=
            (Real.enorm_eq_ofReal_abs _).symm
        _ ≤ ∫⁻ w, ‖f w * (g n w - g0 w)‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
        _ = eLpNorm (fun w => f w * (g n w - g0 w)) 1 μ := (eLpNorm_one_eq_lintegral_enorm (hf.aestronglyMeasurable.mul
              ((hg n).aestronglyMeasurable.sub hg0.aestronglyMeasurable))).symm
        _ ≤ eLpNorm f 2 μ * eLpNorm (fun w => g n w - g0 w) 2 μ := by
            have hH := eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1)
              hf.aestronglyMeasurable ((hg n).aestronglyMeasurable.sub hg0.aestronglyMeasurable)
            have e1 : (f • (g n - g0)) = fun w => f w * (g n w - g0 w) := by
              funext w
              simp only [smul_eq_mul, Pi.mul_apply, Pi.sub_apply]
            rw [e1] at hH
            exact hH
  rw [← tendsto_sub_nhds_zero_iff]
  exact hT.congr fun n => (hdiff n).symm

theorem HasWeakHorizontalGradient.congr_grad {Q : Measure (FieldPair d)} {hQ : IsStationary Q}
    {f : FieldPair d → ℝ} {Df Df' : FieldPair d → Vec d} (hf : HasWeakHorizontalGradient Q hQ f Df)
    (h : ∀ᵐ w ∂Q, Df w = Df' w) : HasWeakHorizontalGradient Q hQ f Df' := by
  obtain ⟨hfi, hDi, hid⟩ := hf
  refine ⟨hfi, fun i => (hDi i).congr (h.mono fun w hw => by simp only [hw]), fun i F G hF hG => ?_⟩
  rw [hid i F G hF hG]
  congr 1
  exact integral_congr_ae (h.mono fun w hw => by simp only [hw])

theorem HasWeakHorizontalDivergence.congr_div {Q : Measure (FieldPair d)} {hQ : IsStationary Q}
    {V : FieldPair d → Vec d} {h h' : FieldPair d → ℝ} (hV : HasWeakHorizontalDivergence Q hQ V h)
    (hh : h =ᵐ[Q] h') : HasWeakHorizontalDivergence Q hQ V h' := by
  obtain ⟨hVi, hhi, hid⟩ := hV
  refine ⟨hVi, hhi.congr hh, fun F hF DF hDF => ?_⟩
  rw [hid F hF DF hDF]
  congr 1
  exact integral_congr_ae (hh.mono fun w hw => by simp only [hw])

/-! ## Smoothing in `L²` -/

theorem unitMassScaledMollifier_nonneg' {ε : ℝ} (hε : 0 < ε) (z : Vec d) :
    0 ≤ Calculus.unitMassScaledMollifier d ε z :=
  mul_nonneg (inv_nonneg.mpr (pow_nonneg hε.le d)) (mollifier_nonneg d _)

theorem integral_unitMassScaledMollifier' {ε : ℝ} (hε : 0 < ε) :
    ∫ z, Calculus.unitMassScaledMollifier d ε z = 1 := by
  unfold Calculus.unitMassScaledMollifier
  rw [integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg (μ := volume) (mollifier d) hε.le,
    Module.finrank_fin_fun, integral_mollifier, smul_eq_mul, mul_one,
    inv_mul_cancel₀ (pow_ne_zero d hε.ne')]

theorem memLp_horizontalMollify_unitMass {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {ε : ℝ} (hε : 0 < ε) {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : q ≠ ⊤)
    {v : FieldPair d → ℝ} (hvm : Measurable v) (hv : MemLp v q Q) :
    MemLp (horizontalMollify (Calculus.unitMassScaledMollifier d ε) v) q Q :=
    (Calculus.eLpNorm_horizontalMollify_le Q hQ q hq
      (contDiff_unitMassScaledMollifier ε).continuous.measurable
      (unitMassScaledMollifier_nonneg' hε) (integral_unitMassScaledMollifier' hε) hvm).trans_lt
      hv.eLpNorm_lt_top

/-- The scales `ε_n = 1 / (n + 2)`. -/
def scaleSeq (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)

theorem scaleSeq_pos (n : ℕ) : 0 < scaleSeq n := by unfold scaleSeq; positivity

theorem scaleSeq_le_one (n : ℕ) : scaleSeq n ≤ 1 := by
  unfold scaleSeq
  rw [div_le_one (by positivity)]
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem tendsto_scaleSeq : Tendsto scaleSeq atTop (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, Filter.Eventually.of_forall scaleSeq_pos⟩
  have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h := h0.comp (tendsto_add_atTop_nat 1)
  refine h.congr fun n => ?_
  simp only [Function.comp, scaleSeq, Nat.cast_add, Nat.cast_one]
  ring

theorem tendsto_eLpNorm_mollify_scaleSeq {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {q : ℝ≥0∞} [Fact (1 ≤ q)] (hq : q ≠ ⊤) {v : FieldPair d → ℝ}
    (hvm : Measurable v) (hv : MemLp v q Q) :
    Tendsto (fun n => eLpNorm (fun w => horizontalMollify
      (Calculus.unitMassScaledMollifier d (scaleSeq n)) v w - v w) q Q) atTop (𝓝 0) :=
  (Calculus.tendsto_eLpNorm_horizontalMollify_unitMassScaledMollifier Q hQ q hq hvm hv).comp
    tendsto_scaleSeq

/-! ## The divergence identity against the truncated density -/

/-- For `M ≥ 1`, testing the weak divergence of `F` against the smoothings `S_ε (T_M ∘ ρ)` and
letting `ε → 0` gives `∑ᵢ E[Fᵢ T_M'(ρ) Dᵢρ] = -E[h T_M(ρ)]`. -/
theorem divergence_identity_truncated {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {rho : FieldPair d → ℝ} (hrhom : Measurable rho)
    {Dm : FieldPair d → Vec d} (hDm : Measurable Dm) (hW : HasWeakHorizontalGradient Q hQ rho Dm)
    {F : FieldPair d → Vec d} (hF2 : ∀ i, MemLp (fun w => F w i) 2 Q)
    {h : FieldPair d → ℝ} (hh2 : MemLp h 2 Q) (hdiv : HasWeakHorizontalDivergence Q hQ F h)
    {M : ℕ} (hM : 1 ≤ M)
    (hv2 : ∀ i, MemLp (fun w => softTruncationDeriv (M : ℝ) (rho w) * Dm w i) 2 Q) :
    ∑ i, ∫ w, F w i * (softTruncationDeriv (M : ℝ) (rho w) * Dm w i) ∂Q =
      -∫ w, h w * softTruncation (M : ℝ) (rho w) ∂Q := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  set u : FieldPair d → ℝ := fun w => softTruncation (M : ℝ) (rho w) with hudef
  set v : Fin d → FieldPair d → ℝ := fun i w => softTruncationDeriv (M : ℝ) (rho w) * Dm w i
    with hvdef
  have hum : Measurable u := (measurable_softTruncation _).comp hrhom
  have huB : ∀ w, |u w| ≤ M := fun w => abs_softTruncation_le_level hM0 _
  have hu2 : MemLp u 2 Q := MemLp.of_bound hum.aestronglyMeasurable (M : ℝ)
    (ae_of_all _ fun w => by rw [Real.norm_eq_abs]; exact huB w)
  have hvm : ∀ i, Measurable (v i) := fun i =>
    ((measurable_softTruncationDeriv _).comp hrhom).mul ((measurable_pi_apply i).comp hDm)
  have hchain := hasWeakHorizontalGradient_softTruncation hQ (M : ℝ) hW
  set ζ : ℕ → Vec d → ℝ := fun n => Calculus.unitMassScaledMollifier d (scaleSeq n) with hζdef
  have hSv2 : ∀ n i, MemLp (horizontalMollify (ζ n) (v i)) 2 Q := fun n i =>
    memLp_horizontalMollify_unitMass hQ (scaleSeq_pos n) ENNReal.ofNat_ne_top (hvm i) (hv2 i)
  have hSu2 : ∀ n, MemLp (horizontalMollify (ζ n) u) 2 Q := fun n =>
    memLp_horizontalMollify_unitMass hQ (scaleSeq_pos n) ENNReal.ofNat_ne_top hum hu2
  have hn : ∀ n, ∑ i, ∫ w, F w i * horizontalMollify (ζ n) (v i) w ∂Q =
      -∫ w, h w * horizontalMollify (ζ n) u w ∂Q := by
    intro n
    have hG : IsHorizontalTest (horizontalMollify (ζ n) u) :=
      Correctors.isHorizontalTest_horizontalMollify _ (contDiff_unitMassScaledMollifier _)
        (hasCompactSupport_unitMassScaledMollifier (scaleSeq_pos n)) u hum ⟨M, huB⟩
    have hI := HasWeakHorizontalDivergence.integral_test hdiv hG
    have hD : ∀ᵐ w ∂Q, ∀ i, horizontalDerivative i (horizontalMollify (ζ n) u) w =
        horizontalMollify (ζ n) (v i) w :=
      ae_all_iff.mpr fun i => Calculus.ae_orbit_derivative_mollify_eq hQ (scaleSeq_pos n)
        (scaleSeq_le_one n) hum (hu2.integrable one_le_two) (hvm i)
        ((hv2 i).integrable one_le_two) i fun K hK => Calculus.weakPairing_core hchain i hK
    have hint : ∀ i, Integrable (fun w => F w i * horizontalMollify (ζ n) (v i) w) Q := fun i =>
      (hF2 i).integrable_mul (hSv2 n i)
    rw [← integral_finset_sum _ fun i _ => hint i, ← hI]
    refine integral_congr_ae ?_
    filter_upwards [hD] with w hw
    exact Finset.sum_congr rfl fun i _ => by rw [hw i]
  have hL : Tendsto (fun n => ∑ i, ∫ w, F w i * horizontalMollify (ζ n) (v i) w ∂Q) atTop
      (𝓝 (∑ i, ∫ w, F w i * v i w ∂Q)) :=
    tendsto_finset_sum _ fun i _ => tendsto_integral_mul_of_eLpNorm_two (hF2 i)
      (fun n => hSv2 n i) (hv2 i)
      (tendsto_eLpNorm_mollify_scaleSeq hQ ENNReal.ofNat_ne_top (hvm i) (hv2 i))
  have hR : Tendsto (fun n => -∫ w, h w * horizontalMollify (ζ n) u w ∂Q) atTop
      (𝓝 (-∫ w, h w * u w ∂Q)) :=
    (tendsto_integral_mul_of_eLpNorm_two hh2 hSu2 hu2
      (tendsto_eLpNorm_mollify_scaleSeq hQ ENNReal.ofNat_ne_top hum hu2)).neg
  exact tendsto_nhds_unique hL (hR.congr fun n => (hn n).symm)

theorem abs_apply_le_euclideanNorm (x : Vec d) (i : Fin d) : |x i| ≤ euclideanNorm x := by
  unfold euclideanNorm euclideanSq dot
  refine Real.abs_le_sqrt ?_
  rw [sq]
  exact Finset.single_le_sum (f := fun j => x j * x j) (fun j _ => mul_self_nonneg _)
    (Finset.mem_univ i)

/-- **Lemma 4.2, second assertion**, for one density (`paper/main.tex` 634-638): for a field `F`
local in `B_r` with `|F| ∈ L^{2p}` and weak divergence `h ∈ L^{2p}`, `E[ρ h] = -E[Dρ · F]`. The
density is smoothed: the tests are `S_ε (T_M ∘ ρ)`. The inputs are the `L²` bound `hv2` on
`T_M'(ρ) Dρ`, the occupation bound on `B_{2r}`, and the integrability in the first assertion on
`B_r`. -/
theorem divergence_second_of_local {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {rho : FieldPair d → ℝ} (hrhom : Measurable rho)
    (hrho0 : ∀ w, 0 ≤ rho w) {Drho : FieldPair d → Vec d}
    (hW : HasWeakHorizontalGradient Q hQ rho Drho)
    (hv2 : ∀ M : ℕ, 1 ≤ M → ∀ i,
      MemLp (fun w => softTruncationDeriv (M : ℝ) (rho w) * Drho w i) 2 Q)
    {r : ℝ} (hr : 0 < r) {p : ℝ} (hp : 1 ≤ p) {K : ℝ}
    (hocc : ∀ G : FieldPair d → ℝ,
      Measurable[localSigma {y : Vec d | euclideanNorm y < 2 * r}] G →
      MemLp G (ENNReal.ofReal p) Q →
      ∫⁻ w, ENNReal.ofReal (rho w) * ENNReal.ofReal |G w| ∂Q ≤
        ENNReal.ofReal K * eLpNorm G (ENNReal.ofReal p) Q)
    (hdiv1 : ∀ V : FieldPair d → Vec d,
      Measurable[localSigma {y : Vec d | euclideanNorm y < r}] V →
      MemLp (fun w => euclideanNorm (V w)) (ENNReal.ofReal (2 * p)) Q →
      Integrable (fun w => dot (Drho w) (V w)) Q)
    {F : FieldPair d → Vec d} (hFl : Measurable[localSigma {y : Vec d | euclideanNorm y < r}] F)
    (hFM : MemLp (fun w => euclideanNorm (F w)) (ENNReal.ofReal (2 * p)) Q)
    {h : FieldPair d → ℝ} (hhM : MemLp h (ENNReal.ofReal (2 * p)) Q)
    (hdiv : HasWeakHorizontalDivergence Q hQ F h) :
    Integrable (fun w => rho w * h w) Q ∧
      ∫ w, rho w * h w ∂Q = -∫ w, dot (Drho w) (F w) ∂Q := by
  set q : ℝ≥0∞ := ENNReal.ofReal (2 * p) with hqdef
  have hq1 : 1 ≤ q := by
    rw [hqdef, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  haveI : Fact (1 ≤ q) := ⟨hq1⟩
  have hqtop : q ≠ ⊤ := ENNReal.ofReal_ne_top
  have hq2 : (2 : ℝ≥0∞) ≤ q := by
    rw [hqdef, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hpq : ENNReal.ofReal p ≤ q := ENNReal.ofReal_le_ofReal (by linarith)
  have hFm : Measurable F := hFl.mono (Probability.localSigma_le_borel _) le_rfl
  have hFq : ∀ i, MemLp (fun w => F w i) q Q := fun i =>
    hFM.of_le ((measurable_pi_apply i).comp hFm).aestronglyMeasurable (ae_of_all _ fun w => by
      have hn : 0 ≤ euclideanNorm (F w) := by unfold euclideanNorm; exact Real.sqrt_nonneg _
      rw [Real.norm_of_nonneg hn, Real.norm_eq_abs]
      exact abs_apply_le_euclideanNorm (F w) i)
  have hF2 : ∀ i, MemLp (fun w => F w i) 2 Q := fun i => (hFq i).mono_exponent hq2
  -- Measurable versions of `h` and `Dρ`.
  set hm := hhM.aestronglyMeasurable.mk h with hmdef
  have hmm : Measurable hm := hhM.aestronglyMeasurable.measurable_mk
  have hhae : h =ᵐ[Q] hm := hhM.aestronglyMeasurable.ae_eq_mk
  have hdiv' := HasWeakHorizontalDivergence.congr_div hdiv hhae
  have hmq : MemLp hm q Q := hhM.ae_eq hhae
  set Dm : FieldPair d → Vec d := fun w i => (hW.2.1 i).1.mk (fun w => Drho w i) w with hDmdef
  have hDm : Measurable Dm := Measurable.of_eval fun i => (hW.2.1 i).1.measurable_mk
  have hDae : ∀ᵐ w ∂Q, Drho w = Dm w := by
    filter_upwards [ae_all_iff.mpr fun i => (hW.2.1 i).1.ae_eq_mk] with w hw
    funext i
    exact hw i
  have hW' := HasWeakHorizontalGradient.congr_grad hW hDae
  have hv2' : ∀ M : ℕ, 1 ≤ M → ∀ i,
      MemLp (fun w => softTruncationDeriv (M : ℝ) (rho w) * Dm w i) 2 Q :=
    fun M hM i => (hv2 M hM i).ae_eq (hDae.mono fun w hw => by simp only [hw])
  -- Locality of `h`, and integrability of `ρ h`.
  obtain ⟨g, hgl, hhg⟩ := exists_local_ae_eq_of_hasWeakHorizontalDivergence hQ
    (show r < 2 * r by linarith) hqtop hFl (fun i => (hFq i).integrable hq1) hmm hmq hdiv'
  have hgp : MemLp g (ENNReal.ofReal p) Q := (hmq.ae_eq hhg).mono_exponent hpq
  have hgm : Measurable g := hgl.mono (Probability.localSigma_le_borel _) le_rfl
  have hρg : Integrable (fun w => rho w * g w) Q := by
    have hlin : ∫⁻ w, ‖rho w * g w‖ₑ ∂Q =
        ∫⁻ w, ENNReal.ofReal (rho w) * ENNReal.ofReal |g w| ∂Q :=
      lintegral_congr fun w => by
        rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg (hrho0 w),
          ENNReal.ofReal_mul (hrho0 w)]
    refine ⟨(hrhom.mul hgm).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    rw [hlin]
    exact lt_of_le_of_lt (hocc g hgl hgp)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hgp.eLpNorm_lt_top)
  have hρhm : Integrable (fun w => rho w * hm w) Q :=
    hρg.congr (hhg.mono fun w hw => by simp only [hw])
  have hρh : Integrable (fun w => rho w * h w) Q :=
    hρhm.congr (hhae.mono fun w hw => by simp only [hw])
  refine ⟨hρh, ?_⟩
  -- The identities for the truncations.
  have hstep : ∀ M : ℕ, 1 ≤ M →
      ∑ i, ∫ w, F w i * (softTruncationDeriv (M : ℝ) (rho w) * Dm w i) ∂Q =
        -∫ w, hm w * softTruncation (M : ℝ) (rho w) ∂Q :=
    fun M hM => divergence_identity_truncated hQ hrhom hDm hW' hF2 (hmq.mono_exponent hq2) hdiv'
      hM (hv2' M hM)
  -- Integrability of `Fᵢ Dᵢρ`, from the first assertion with `V = Fᵢ eᵢ`.
  have hFD : ∀ i, Integrable (fun w => F w i * Dm w i) Q := by
    intro i
    set V : FieldPair d → Vec d := fun w k => if k = i then F w i else 0 with hVdef
    have hVl : Measurable[localSigma {y : Vec d | euclideanNorm y < r}] V := by
      letI : MeasurableSpace (FieldPair d) := localSigma {y : Vec d | euclideanNorm y < r}
      refine Measurable.of_eval fun k => ?_
      by_cases hk : k = i
      · simp only [hVdef, hk, if_true]
        exact (measurable_pi_apply i).comp hFl
      · simp only [hVdef, hk, if_false]
        exact measurable_const
    have he : ∀ w, euclideanNorm (V w) = |F w i| := fun w => by
      unfold euclideanNorm euclideanSq dot
      rw [Finset.sum_eq_single i (fun k _ hk => by simp [hVdef, hk]) (by simp)]
      simp only [hVdef, if_pos rfl]
      exact Real.sqrt_mul_self_eq_abs _
    have hVM : MemLp (fun w => euclideanNorm (V w)) q Q := by
      have e : (fun w => euclideanNorm (V w)) = fun w => |F w i| := funext he
      rw [e]
      exact (hFq i).abs
    have h1 := hdiv1 V hVl hVM
    have e2 : (fun w => dot (Drho w) (V w)) = fun w => Drho w i * F w i := by
      funext w
      unfold dot
      rw [Finset.sum_eq_single i (fun k _ hk => by simp [hVdef, hk]) (by simp)]
      simp only [hVdef, if_pos rfl]
    rw [e2] at h1
    exact h1.congr (hDae.mono fun w hw => by simp only [hw, mul_comm])
  -- The limits `M → ∞`.
  have hA : Tendsto (fun M : ℕ =>
      ∑ i, ∫ w, F w i * (softTruncationDeriv (M : ℝ) (rho w) * Dm w i) ∂Q) atTop
      (𝓝 (∑ i, ∫ w, F w i * Dm w i ∂Q)) := by
    refine tendsto_finset_sum _ fun i _ => ?_
    refine tendsto_integral_of_dominated_convergence (fun w => |F w i * Dm w i|)
      (fun M => ?_) (hFD i).abs (fun M => ae_of_all _ fun w => ?_) (ae_of_all _ fun w => ?_)
    · exact (((measurable_pi_apply i).comp hFm).mul (((measurable_softTruncationDeriv _).comp
        hrhom).mul ((measurable_pi_apply i).comp hDm))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, show F w i * (softTruncationDeriv (M : ℝ) (rho w) * Dm w i) =
        softTruncationDeriv (M : ℝ) (rho w) * (F w i * Dm w i) by ring, abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (abs_softTruncationDeriv_le_one _ _)
    · have h1 := (tendsto_softTruncationDeriv (rho w)).mul_const (F w i * Dm w i)
      rw [one_mul] at h1
      exact h1.congr fun M => by ring
  have hB : Tendsto (fun M : ℕ => -∫ w, hm w * softTruncation (M : ℝ) (rho w) ∂Q) atTop
      (𝓝 (-∫ w, hm w * rho w ∂Q)) := by
    refine Tendsto.neg ?_
    refine tendsto_integral_of_dominated_convergence (fun w => |rho w * hm w|) (fun M => ?_)
      hρhm.abs (fun M => ae_of_all _ fun w => ?_) (ae_of_all _ fun w => ?_)
    · exact (hmm.mul ((measurable_softTruncation _).comp hrhom)).aestronglyMeasurable
    · show ‖hm w * softTruncation (M : ℝ) (rho w)‖ ≤ |rho w * hm w|
      rw [Real.norm_eq_abs, abs_mul, abs_mul, mul_comm (|rho w|)]
      exact mul_le_mul_of_nonneg_left (abs_softTruncation_le _ _) (abs_nonneg _)
    · exact (tendsto_softTruncation (rho w)).const_mul (hm w)
  have hEq : ∑ i, ∫ w, F w i * Dm w i ∂Q = -∫ w, hm w * rho w ∂Q :=
    tendsto_nhds_unique_of_eventuallyEq hA hB
      ((eventually_ge_atTop 1).mono fun M hM => hstep M hM)
  have hdot : ∫ w, dot (Drho w) (F w) ∂Q = ∑ i, ∫ w, F w i * Dm w i ∂Q := by
    rw [← integral_finset_sum _ fun i _ => hFD i]
    refine integral_congr_ae (hDae.mono fun w hw => ?_)
    simp only [dot, hw]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hrh : ∫ w, rho w * h w ∂Q = ∫ w, hm w * rho w ∂Q :=
    integral_congr_ae (hhae.mono fun w hw => by simp only [hw, mul_comm])
  rw [hrh, hdot, hEq, neg_neg]

/-! ## The `L²` bound on `T_M'(ρ) Dρ` from the Fisher bound -/

theorem mul_softTruncationDeriv_sq_le {M : ℝ} (hM : 0 < M) {x : ℝ} (hx : 0 ≤ x) :
    x * softTruncationDeriv M x ^ 2 ≤ M := by
  set t := x / M with htdef
  have ht : 0 ≤ t := div_nonneg hx hM.le
  have hxt : x = M * t := by rw [htdef]; field_simp
  have hpos : 0 < 1 + t * t := one_add_mul_self_pos t
  have h1 : (1 - t * t) ^ 2 ≤ ((1 + t * t) ^ 2) := by nlinarith [mul_self_nonneg t]
  have h2 : t ≤ (1 + t * t) ^ 2 := by nlinarith [mul_self_nonneg t, mul_self_nonneg (t - 1)]
  have key : t * ((1 - t * t) / (1 + t * t) ^ 2) ^ 2 ≤ 1 := by
    rw [div_pow, mul_div_assoc', div_le_one (by positivity)]
    calc t * (1 - t * t) ^ 2 ≤ (1 + t * t) ^ 2 * (1 + t * t) ^ 2 :=
          mul_le_mul h2 h1 (sq_nonneg _) (sq_nonneg _)
      _ = ((1 + t * t) ^ 2) ^ 2 := by ring
  unfold softTruncationDeriv
  rw [← htdef, hxt]
  calc M * t * ((1 - t * t) / (1 + t * t) ^ 2) ^ 2 =
        M * (t * ((1 - t * t) / (1 + t * t) ^ 2) ^ 2) := by ring
    _ ≤ M * 1 := mul_le_mul_of_nonneg_left key hM.le
    _ = M := mul_one M

/-- The truncated gradient `T_M'(ρ) Dᵢρ` is in `L²` under the Fisher bound of Lemma 4.1. -/
theorem memLp_two_softTruncationDeriv_mul_grad {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hQ : IsStationary (Carriers.reducedReferenceLaw Q)) {rho : FieldPair d → ℝ}
    (hrho0 : ∀ w, 0 ≤ rho w) (hrhom : Measurable rho) {Drho Drho₀ : FieldPair d → Vec d}
    (hW : HasWeakHorizontalGradient (Carriers.reducedReferenceLaw Q) hQ rho Drho)
    (hW₀ : HasWeakHorizontalGradient (Carriers.reducedReferenceLaw Q) hQ rho Drho₀) {B : ℝ}
    (hK₀ : (∫⁻ w, ENNReal.ofReal
        (if rho w = 0 then 0 else dot (Drho₀ w) ((w.1 0).mulVec (Drho₀ w)) / rho w)
        ∂(Carriers.reducedReferenceLaw Q)) ≤ ENNReal.ofReal B)
    {M : ℕ} (hM : 1 ≤ M) (i : Fin d) :
    MemLp (fun w => softTruncationDeriv (M : ℝ) (rho w) * Drho w i) 2
      (Carriers.reducedReferenceLaw Q) := by
  set μ := Carriers.reducedReferenceLaw Q with hμdef
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  set Λ := sourceReducedBound Λ₀ with hΛdef
  have hΛ : 0 < Λ := sourceReducedBound_pos_of_one_le Q.ellipticity_parameter
  have hzero := hzero_of_weakChainRule hasWeakChainRule_truncProfile_reduced Q hQ rho Drho hW
  have hae0 : ∀ᵐ w ∂μ, Drho w = Drho₀ w := by
    filter_upwards [ae_all_iff.mpr fun j => HasWeakHorizontalGradient.ae_unique hW hW₀ j]
      with w hw
    funext j
    exact hw j
  have hell := ae_reduced_elliptic_zero Q
  have hgm : AEStronglyMeasurable (fun w => softTruncationDeriv (M : ℝ) (rho w) * Drho w i) μ :=
    ((measurable_softTruncationDeriv _).comp hrhom).aestronglyMeasurable.mul (hW.2.1 i).1
  rw [memLp_two_iff_integrable_sq hgm]
  refine ⟨hgm.pow 2, ?_⟩
  unfold HasFiniteIntegral
  show ∫⁻ w, ‖(softTruncationDeriv (M : ℝ) (rho w) * Drho w i) ^ 2‖ₑ ∂μ < ⊤
  have hbound : ∀ᵐ w ∂μ, ‖(softTruncationDeriv (M : ℝ) (rho w) * Drho w i) ^ 2‖ₑ ≤
      ENNReal.ofReal (M * Λ) * ENNReal.ofReal
        (if rho w = 0 then 0 else dot (Drho₀ w) ((w.1 0).mulVec (Drho₀ w)) / rho w) := by
    filter_upwards [hzero, hae0, hell] with w hz he hl
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (sq_nonneg _),
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    by_cases h0 : rho w = 0
    · rw [hz h0, if_pos h0]
      simp
    · rw [if_neg h0, he]
      have hρpos : 0 < rho w := lt_of_le_of_ne (hrho0 w) (Ne.symm h0)
      set ξ := Drho₀ w with hξdef
      have hsqnn : 0 ≤ euclideanSq ξ := by
        unfold euclideanSq dot
        exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
      have hsq : ξ i ^ 2 ≤ euclideanSq ξ := by
        unfold euclideanSq dot
        rw [sq]
        exact Finset.single_le_sum (f := fun j => ξ j * ξ j)
          (fun j _ => mul_self_nonneg _) (Finset.mem_univ i)
      have hl1 := (hl.2 ξ).1
      have hel : euclideanSq ξ ≤ Λ * dot ξ ((w.1 0).mulVec ξ) := by
        have h2 := mul_le_mul_of_nonneg_left hl1 hΛ.le
        rwa [← mul_assoc, mul_inv_cancel₀ hΛ.ne', one_mul] at h2
      have hD : 0 ≤ dot ξ ((w.1 0).mulVec ξ) :=
        le_trans (mul_nonneg (inv_nonneg.mpr hΛ.le) hsqnn) hl1
      have hT := mul_softTruncationDeriv_sq_le hM0 (hrho0 w)
      set T := softTruncationDeriv (M : ℝ) (rho w) with hTdef
      set D := dot ξ ((w.1 0).mulVec ξ) with hDdef
      have hfac : T ^ 2 * (Λ * D) = (rho w * T ^ 2) * Λ * (D / rho w) := by
        field_simp
      calc (T * ξ i) ^ 2 = T ^ 2 * ξ i ^ 2 := by ring
        _ ≤ T ^ 2 * (Λ * D) := mul_le_mul_of_nonneg_left (hsq.trans hel) (sq_nonneg _)
        _ = (rho w * T ^ 2) * Λ * (D / rho w) := hfac
        _ ≤ M * Λ * (D / rho w) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hT hΛ.le)
            (div_nonneg hD hρpos.le)
  refine lt_of_le_of_lt (lintegral_mono_ae hbound) ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_of_le_of_lt hK₀ ENNReal.ofReal_lt_top)

/-! ## Lemma 4.2 -/

section Assembly

open EinsteinRelation.Carriers

/-- **Lemma 4.2** (`entropy.divergence`, `paper/main.tex` 619-638), both assertions, from the
Fisher bound of Lemma 4.1 (`hFisher`) and the occupation bound of Proposition 3.2 (`hOcc`), in the
forms of `divergence_bound_of_fisher_occupation''`. The first assertion is that theorem; the
second is `divergence_second_of_local`, on the ball `B_{l/(2λ)}` with the occupation bound on
`B_{l/λ}`. -/
theorem divergenceStatement_of_fisher_occupation (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ)
    (hFisher : ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
      ∀ Q : EnvironmentLaw d Λ₀ r₀, ∀ (hQ : IsStationary (reducedReferenceLaw Q)),
      ∀ lam : ℝ, ∀ hl0 : 0 < lam, ∀ hl1 : lam ≤ 1,
      ∀ (P : QuenchedPathLaws d)
        (origin_probability : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P ω)),
        IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam hl0.le hl1 (originLaw P) →
      ∀ s : {r : ℝ // 0 < r}, ∀ rho : FieldPair d → ℝ,
        IsReducedLaplaceDensity Q.measure P origin_probability s rho →
        ∃ Drho : FieldPair d → Vec d,
          HasWeakHorizontalGradient (reducedReferenceLaw Q) hQ rho Drho ∧
          Integrable (fun w => euclideanNorm (Drho w)) (reducedReferenceLaw Q) ∧
          (∫⁻ w, ENNReal.ofReal
              (if rho w = 0 then 0 else dot (Drho w) ((w.1 0).mulVec (Drho w)) / rho w)
              ∂(reducedReferenceLaw Q)) ≤
            ENNReal.ofReal (4 * sourceReducedBound Λ₀ * lam ^ 2))
    (hOcc : ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ), 1 ≤ Λ₀ → 1 ≤ r₀ →
      ∃ l₀ : ℝ, r₀ < 2 * l₀ ∧ ∀ l : ℝ, l₀ ≤ l →
      ∃ p₀ : ℝ, 1 < p₀ ∧ ∀ p : ℝ, p₀ ≤ p →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ Q : EnvironmentLaw d Λ₀ r₀, ∀ lam : ℝ, ∀ hl0 : 0 < lam, ∀ hl1 : lam ≤ 1,
        ∀ (P : QuenchedPathLaws d)
          (origin_probability : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P ω)),
          IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam hl0.le hl1 (originLaw P) →
        ∀ G : FieldPair d → ℝ,
          Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] G →
          MemLp G (ENNReal.ofReal p) (reducedReferenceLaw Q) →
        ∀ T : ℝ, 0 < T → ∀ s : {r : ℝ // 0 < r},
          (∫⁻ z : FieldPair d × Path d,
              (∫⁻ t in Set.Icc (0 : ℝ) T, ENNReal.ofReal |G (reducedObservationAt t.toNNReal z)|)
            ∂(annealedCoordinateJoint Q.measure P origin_probability)) ≤
              ENNReal.ofReal (C * (T + (lam ^ 2)⁻¹)) *
                eLpNorm G (ENNReal.ofReal p) (reducedReferenceLaw Q) ∧
          ∀ rho : FieldPair d → ℝ, IsReducedLaplaceDensity Q.measure P origin_probability s rho →
            (∫⁻ w, ENNReal.ofReal (rho w) * ENNReal.ofReal |G w| ∂(reducedReferenceLaw Q)) ≤
              ENNReal.ofReal (C * (1 + s.1 * (lam ^ 2)⁻¹)) *
                eLpNorm G (ENNReal.ofReal p) (reducedReferenceLaw Q)) :
    DivergenceStatement d hd Λ₀ r₀ := by
  unfold DivergenceStatement
  by_cases hΛ : 1 ≤ Λ₀ ∧ 1 ≤ r₀
  swap
  · obtain ⟨l1, hr1, -⟩ := divergence_bound_of_fisher_occupation'' d hd Λ₀ r₀ hFisher hOcc
    refine ⟨l1, hr1, fun l _ => ⟨2, by norm_num, fun p _ => ⟨0, le_rfl, fun Q => ?_⟩⟩⟩
    exact absurd ⟨Q.ellipticity_parameter, Q.range_parameter⟩ hΛ
  obtain ⟨hΛ₀, hr₀⟩ := hΛ
  obtain ⟨l1, hr1, h1⟩ := divergence_bound_of_fisher_occupation'' d hd Λ₀ r₀ hFisher hOcc
  obtain ⟨lO, hrO, hO⟩ := hOcc d hd Λ₀ r₀ hΛ₀ hr₀
  refine ⟨max l1 lO, by linarith [le_max_left l1 lO], fun l hl => ?_⟩
  have hl1 : l1 ≤ l := le_trans (le_max_left _ _) hl
  have hlO : lO ≤ l := le_trans (le_max_right _ _) hl
  have hlpos : 0 < l := by linarith
  obtain ⟨p1, hp1, h1'⟩ := h1 l hl1
  obtain ⟨pO, hpO, hO'⟩ := hO l hlO
  refine ⟨max p1 pO, lt_of_lt_of_le hp1 (le_max_left _ _), fun p hp => ?_⟩
  have hp1' : p1 ≤ p := le_trans (le_max_left _ _) hp
  have hpO' : pO ≤ p := le_trans (le_max_right _ _) hp
  have hp1'' : 1 ≤ p := by linarith
  obtain ⟨C1, hC1, hb⟩ := h1' p hp1'
  obtain ⟨CO, hCO, hOb⟩ := hO' p hpO'
  refine ⟨C1, hC1, ?_⟩
  intro Q hQ lam hl0 hll1 IQ P op hyp s hs rho hrho Drho hDrho F hFl hFM
  obtain ⟨rfl, hGMP⟩ := hyp
  have hfirst := hb Q hQ lam hl0 hll1 P op hGMP s hs rho hrho Drho hDrho
  refine ⟨hfirst F hFl hFM, fun h hhM hdiv => ?_⟩
  have hr : 0 < l / (2 * lam) := by positivity
  have hrad : l / lam = 2 * (l / (2 * lam)) := by field_simp
  obtain ⟨Drho₀, hW₀, -, hK₀⟩ := hFisher d hd Λ₀ r₀ Q hQ lam hl0 hll1 P op hGMP s rho hrho
  exact divergence_second_of_local hQ hrho.1 hrho.2.1 hDrho
    (fun M hM i => memLp_two_softTruncationDeriv_mul_grad Q hQ hrho.2.1 hrho.1 hDrho hW₀ hK₀ hM i)
    hr hp1'' (K := CO * (1 + s.1 * (lam ^ 2)⁻¹))
    (fun G hGl hGp => (hOb Q lam hl0 hll1 P op hGMP G (by rw [hrad]; exact hGl) hGp 1 one_pos
      s).2 rho hrho)
    (fun V hVl hVp => (hfirst V hVl hVp).1) hFl hFM hhM hdiv

end Assembly

end EinsteinRelation.Entropy
