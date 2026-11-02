import EinsteinFull.Calculus.C8GMPRealizationExists
import EinsteinFull.Calculus.S4PhysicalWellPosedSupport
import MarkovProcess.Semigroup.ResolventGeneration
import MarkovProcess.Semigroup.GeneratorClosed
import MarkovProcess.Semigroup.PoissonInvariant
import MarkovProcess.Kernel.PositiveC0Resolvent
import MarkovProcess.Examples.HeatSemigroup
import MarkovProcess.Kernel.OnePointKolmogorov
import MarkovProcess.Kernel.OnePointKilled
import MarkovProcess.Kernel.OnePointConservative
import MarkovProcess.Killed.GluingLocal
import MarkovProcess.Main
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Integral.IntervalAverage

/-! # The physical weighted-H¹ semigroup

The resolvent of the full physical form generates a strongly continuous
contraction semigroup on the actual physical reversible L² space. These
operators retain the original variational resolvent; identifying their
spatial kernels and continuous path laws is a separate proof obligation.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

noncomputable section

namespace EinsteinFull.Blueprint

open EinsteinRelation EinsteinRelation.External.GantertSection7Support
open MarkovProcess.Semigroup

private theorem closedForm_energySublevel_isClosed {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (E : SubdiffusiveProcess.DirichletForm.ClosedForm μ) (K : ℝ) :
    IsClosed {u : Lp ℝ 2 μ | u ∈ E.domain ∧ E.form u u ≤ K} := IsSeqClosed.isClosed <| by
    intro us u hus hlim
    exact E.mem_domain_of_tendsto_of_form_le (fun n => (hus n).1) hlim
      (fun n => (hus n).2)

private theorem closedForm_energySublevel_convex {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (E : SubdiffusiveProcess.DirichletForm.ClosedForm μ) (K : ℝ) :
    Convex ℝ {u : Lp ℝ 2 μ | u ∈ E.domain ∧ E.form u u ≤ K} := by
    intro u hu v hv a b ha hb hab
    have hau := E.domain.smul_mem a hu.1
    have hbv := E.domain.smul_mem b hv.1
    refine ⟨E.domain.add_mem hau hbv, ?_⟩
    have hp := E.form_nonneg (u - v) (E.domain.sub_mem hu.1 hv.1)
    rw [E.form_sub_self hu.1 hv.1] at hp
    rw [E.form_add_self hau hbv,
      E.form_smul_left a u hu.1 (a • u) hau, E.form_smul_right a hu.1 hu.1,
      E.form_smul_left a u hu.1 (b • v) hbv, E.form_smul_right b hu.1 hv.1,
      E.form_smul_left b v hv.1 (b • v) hbv, E.form_smul_right b hv.1 hv.1]
    calc
      a * (a * E.form u u) + 2 * (a * (b * E.form u v)) + b * (b * E.form v v) ≤
          a * E.form u u + b * E.form v v := by
        calc
          _ = a * E.form u u + b * E.form v v -
              a * b * (E.form u u - 2 * E.form u v + E.form v v) := by
            linear_combination (a * E.form u u + b * E.form v v) * hab
          _ ≤ _ := sub_le_self _ (mul_nonneg (mul_nonneg ha hb) hp)
      _ ≤ a * K + b * K :=
        add_le_add (mul_le_mul_of_nonneg_left hu.2 ha)
          (mul_le_mul_of_nonneg_left hv.2 hb)
      _ = K := by rw [← add_mul, hab, one_mul]

/-- The epigraph of a closed form is closed in the ambient product space. -/
private theorem closedForm_energyEpigraph_isClosed {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (E : SubdiffusiveProcess.DirichletForm.ClosedForm μ) :
    IsClosed {p : Lp ℝ 2 μ × ℝ | p.1 ∈ E.domain ∧ E.form p.1 p.1 ≤ p.2} :=
  IsSeqClosed.isClosed <| by
    intro ps p hps hp
    have hfirst : Tendsto (fun n => (ps n).1) atTop (𝓝 p.1) :=
      (continuous_fst.tendsto p).comp hp
    have hsecond : Tendsto (fun n => (ps n).2) atTop (𝓝 p.2) :=
      (continuous_snd.tendsto p).comp hp
    have hbound (ε : ℝ) (hε : 0 < ε) :
        p.1 ∈ E.domain ∧ E.form p.1 p.1 ≤ p.2 + ε := by
      apply (closedForm_energySublevel_isClosed E (p.2 + ε)).mem_of_tendsto hfirst
      filter_upwards [(tendsto_order.1 hsecond).2 (p.2 + ε) (lt_add_of_pos_right _ hε)]
        with n hn
      exact ⟨(hps n).1, (hps n).2.trans hn.le⟩
    refine ⟨(hbound 1 zero_lt_one).1, ?_⟩
    exact le_of_forall_pos_le_add fun ε hε => (hbound ε hε).2

/-- The epigraph of the full closed-form energy is convex. -/
private theorem closedForm_energyEpigraph_convex {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (E : SubdiffusiveProcess.DirichletForm.ClosedForm μ) :
    Convex ℝ {p : Lp ℝ 2 μ × ℝ | p.1 ∈ E.domain ∧ E.form p.1 p.1 ≤ p.2} := by
  intro u hu v hv a b ha hb hab
  have hau := E.domain.smul_mem a hu.1
  have hbv := E.domain.smul_mem b hv.1
  refine ⟨E.domain.add_mem hau hbv, ?_⟩
  have hp := E.form_nonneg (u.1 - v.1) (E.domain.sub_mem hu.1 hv.1)
  rw [E.form_sub_self hu.1 hv.1] at hp
  change E.form (a • u.1 + b • v.1) (a • u.1 + b • v.1) ≤ a * u.2 + b * v.2
  rw [E.form_add_self hau hbv,
    E.form_smul_left a u.1 hu.1 (a • u.1) hau, E.form_smul_right a hu.1 hu.1,
    E.form_smul_left a u.1 hu.1 (b • v.1) hbv, E.form_smul_right b hu.1 hv.1,
    E.form_smul_left b v.1 hv.1 (b • v.1) hbv, E.form_smul_right b hv.1 hv.1]
  calc
    _ = a * E.form u.1 u.1 + b * E.form v.1 v.1 -
        a * b * (E.form u.1 u.1 - 2 * E.form u.1 v.1 + E.form v.1 v.1) := by
      linear_combination (a * E.form u.1 u.1 + b * E.form v.1 v.1) * hab
    _ ≤ a * E.form u.1 u.1 + b * E.form v.1 v.1 :=
      sub_le_self _ (mul_nonneg (mul_nonneg ha hb) hp)
    _ ≤ a * u.2 + b * v.2 :=
      add_le_add (mul_le_mul_of_nonneg_left hu.2 ha) (mul_le_mul_of_nonneg_left hv.2 hb)

/-- Jensen's inequality for the energy of a closed form. -/
private theorem closedForm_energy_setAverage_le {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (E : SubdiffusiveProcess.DirichletForm.ClosedForm μ)
    {α : Type*} [MeasurableSpace α] {ν : Measure α} {A : Set α}
    (h0 : ν A ≠ 0) (htop : ν A ≠ ∞) (u : α → Lp ℝ 2 μ)
    (hu : IntegrableOn u A ν)
    (he : IntegrableOn (fun x => E.form (u x) (u x)) A ν)
    (hdom : ∀ᵐ x ∂ν.restrict A, u x ∈ E.domain) :
    (⨍ x in A, u x ∂ν) ∈ E.domain ∧
      E.form (⨍ x in A, u x ∂ν) (⨍ x in A, u x ∂ν) ≤
        ⨍ x in A, E.form (u x) (u x) ∂ν := by
  have h := (closedForm_energyEpigraph_convex E).set_average_mem
    (closedForm_energyEpigraph_isClosed E) h0 htop
    (hdom.mono fun x hx => ⟨hx, le_rfl⟩) (hu.prodMk he)
  rw [average_pair hu he] at h
  exact h

/-- The actual full physical variational resolvents form a contractive family. -/
def gmpPhysicalContractiveResolvent {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ContractiveResolvent (Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) where
  operator α := gmpPhysicalResolvent hd ω lam Λ hΛ hω α α.property
  resolvent_identity α β := by
    apply ContinuousLinearMap.ext
    intro f
    exact gmpPhysicalResolvent_identity hd ω lam Λ hΛ hω α β α.property β.property f
  opNorm_le_inv α := by
    apply (gmpPhysicalResolvent hd ω lam Λ hΛ hω α α.property).opNorm_le_bound
      (inv_nonneg.mpr α.property.le)
    intro f
    simpa only [div_eq_mul_inv, mul_comm] using
      gmpPhysicalResolvent_norm_le hd ω lam Λ hΛ hω α α.property f
  denseRange α :=
    gmpPhysicalResolvent_denseRange hd ω lam Λ hΛ hω α α.property

/-- The actual physical C₀ resolvents form a contractive family. -/
def gmpPhysicalC0ContractiveResolvent {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) :
    ContractiveResolvent (ZeroAtInftyContinuousMap (Vec d) ℝ) where
  operator α := gmpPhysicalC0Resolvent hd ω lam Λ hΛ hω hSmooth α α.property
  resolvent_identity α β := by
    apply ContinuousLinearMap.ext
    intro f
    exact gmpPhysicalC0Resolvent_identity hd ω lam Λ hΛ hω hSmooth
      α β α.property β.property f
  opNorm_le_inv α :=
    gmpPhysicalC0Resolvent_norm_le hd ω lam Λ hΛ hω hSmooth α α.property
  denseRange α :=
    gmpPhysicalC0Resolvent_denseRange hd ω lam Λ hΛ hω hSmooth α α.property

/-- The C₀ evolution generated by the actual physical resolvent. -/
def gmpPhysicalC0Semigroup {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) :
    StronglyContinuousContractionSemigroup (ZeroAtInftyContinuousMap (Vec d) ℝ) :=
  (gmpPhysicalC0ContractiveResolvent hd ω lam Λ hΛ hω hSmooth).generatedSemigroup

/-- The generated C₀ evolution retains the actual physical resolvent. -/
theorem gmpPhysicalC0Semigroup_resolvent {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (α : PositiveShift) :
    (gmpPhysicalC0Semigroup hd ω lam Λ hΛ hω hSmooth).resolvent α =
      gmpPhysicalC0Resolvent hd ω lam Λ hΛ hω hSmooth α α.property :=
  (gmpPhysicalC0ContractiveResolvent hd ω lam Λ hΛ hω hSmooth).resolvent_generatedSemigroup α

/-- The physical C₀ resolvent preserves pointwise nonnegativity. -/
theorem gmpPhysicalC0Resolvent_positive {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (α : ℝ) (hα : 0 < α)
    (f : ZeroAtInftyContinuousMap (Vec d) ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∀ x, 0 ≤ gmpPhysicalC0Resolvent hd ω lam Λ hΛ hω hSmooth α hα f x := by
  let R := gmpPhysicalC0Resolvent hd ω lam Λ hΛ hω hSmooth α hα
  have hcompact (g : ZeroAtInftyContinuousMap (Vec d) ℝ)
      (hg : HasCompactSupport (g : Vec d → ℝ)) (hgp : ∀ x, 0 ≤ g x) :
      ∀ x, 0 ≤ R g x := by
    have hm := gmpPhysical_compactContinuous_memLp hd ω lam (g : Vec d → ℝ) g.continuous hg
    let G := hm.toLp (g : Vec d → ℝ)
    have hG : (G : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] g := hm.coeFn_toLp
    have hp : 0 ≤ᵐ[physicalReversibleMeasure ω hd lam] G := by
      filter_upwards [hG] with x hx
      simpa only [hx, Pi.zero_apply] using hgp x
    have he := gmpPhysicalC0Resolvent_ae_of_memLp hd ω lam Λ hΛ hω hSmooth α hα g G hG
    have hpos := gmpPhysicalResolvent_positive hd ω lam Λ hΛ hω α hα hp
    have hae : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, 0 ≤ R g x := by
      filter_upwards [he, hpos] with x hx hxpos
      change R g x = _ at hx
      rw [hx]
      exact hxpos
    have hv := (gmpPhysical_ae_iff_volume hd ω lam _).mp hae
    have hc : IsClosed {x : Vec d | 0 ≤ R g x} :=
      isClosed_le continuous_const (R g).continuous
    have hfull : {x : Vec d | 0 ≤ R g x} = Set.univ :=
      (hc.ae_eq_univ_iff_eq (μ := volume)).mp (ae_eq_univ.mpr hv)
    intro x
    have hx : x ∈ {x : Vec d | 0 ≤ R g x} := by rw [hfull]; exact Set.mem_univ x
    exact hx
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    simpa [ε] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  choose g hgc hgb hgK hga using fun n : ℕ =>
    gmpC0_exists_bounded_compact_cutoff f ∅ isCompact_empty (hε n)
  let fn : ℕ → ZeroAtInftyContinuousMap (Vec d) ℝ := fun n => f * g n
  have hb (n : ℕ) : ‖fn n - f‖ ≤ ε n := by
    change ‖(fn n - f).toBCF‖ ≤ ε n
    apply (BoundedContinuousFunction.norm_le (le_of_lt (hε n))).2
    intro x
    change ‖(f * g n) x - f x‖ ≤ ε n
    simpa only [Real.norm_eq_abs] using hga n x
  have hconv : Tendsto fn atTop (𝓝 f) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun n => norm_nonneg _) hb hεlim
  intro x
  have heval : Continuous (fun v : ZeroAtInftyContinuousMap (Vec d) ℝ => v x) :=
    (BoundedContinuousFunction.lipschitz_eval_const x).continuous.comp
      (ZeroAtInftyContinuousMap.isometry_toBCF.continuous)
  have hlim : Tendsto (fun n => R (fn n) x) atTop (𝓝 (R f x)) :=
    (heval.tendsto (R f)).comp (R.continuous.tendsto f |>.comp hconv)
  apply ge_of_tendsto' hlim
  intro n
  apply hcompact (fn n) (HasCompactSupport.mul_left (hgc n))
  intro y
  change 0 ≤ f y * g n y
  exact mul_nonneg (hf y) (hgb n y).1

/-- The physical C₀ evolution preserves pointwise nonnegativity. -/
theorem gmpPhysicalC0Semigroup_positive {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0)
    (f : ZeroAtInftyContinuousMap (Vec d) ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∀ x, 0 ≤ (gmpPhysicalC0Semigroup hd ω lam Λ hΛ hω hSmooth) t f x := by
  let R := gmpPhysicalC0ContractiveResolvent hd ω lam Λ hΛ hω hSmooth
  let C : Set (ZeroAtInftyContinuousMap (Vec d) ℝ) := {f | ∀ x, 0 ≤ f x}
  have hc : IsClosed C := by
    have heq : C = ⋂ x : Vec d, {f : ZeroAtInftyContinuousMap (Vec d) ℝ | 0 ≤ f x} := by
      ext u
      simp only [C, Set.mem_setOf_eq, Set.mem_iInter]
    rw [heq]
    apply isClosed_iInter
    intro x
    exact isClosed_le continuous_const
      ((BoundedContinuousFunction.lipschitz_eval_const x).continuous.comp
        ZeroAtInftyContinuousMap.isometry_toBCF.continuous)
  have hv : Convex ℝ C := by
    intro u hu v hv a b ha hb hab x
    change 0 ≤ a * u x + b * v x
    exact add_nonneg (mul_nonneg ha (hu x)) (mul_nonneg hb (hv x))
  have hz : (0 : ZeroAtInftyContinuousMap (Vec d) ℝ) ∈ C := by
    intro x
    exact le_rfl
  have hQ (α : PositiveShift) : PreservesSet (R.scaledOperator α) C C := by
    intro u hu x
    change 0 ≤ (α : ℝ) * gmpPhysicalC0Resolvent hd ω lam Λ hΛ hω hSmooth α α.property u x
    exact mul_nonneg α.property.le
      (gmpPhysicalC0Resolvent_positive hd ω lam Λ hΛ hω hSmooth α α.property u hu x)
  exact R.preservesSet_generatedSemigroup_of_scaledOperator C hc hv hz hQ t hf

/-- The physical C₀ resolvent identity as an equality of operators. -/
theorem gmpPhysicalC0Resolvent_operator_identity {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (α β : PositiveShift) :
    gmpPhysicalC0Resolvent hd ω lam Λ hΛ hω hSmooth α α.property -
        gmpPhysicalC0Resolvent hd ω lam Λ hΛ hω hSmooth β β.property =
      ((β : ℝ) - (α : ℝ)) •
        (gmpPhysicalC0Resolvent hd ω lam Λ hΛ hω hSmooth α α.property).comp
          (gmpPhysicalC0Resolvent hd ω lam Λ hΛ hω hSmooth β β.property) := by
  apply ContinuousLinearMap.ext
  intro f
  exact gmpPhysicalC0Resolvent_identity hd ω lam Λ hΛ hω hSmooth
    α β α.property β.property f

/-- The physical C₀ resolvent is a positive contractive resolvent. -/
def gmpPhysicalPositiveC0Resolvent {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) :
    MarkovProcess.PositiveC0ContractiveResolvent (Vec d) where
  toContractiveResolvent := gmpPhysicalC0ContractiveResolvent hd ω lam Λ hΛ hω hSmooth
  isPositive α f hf :=
    gmpPhysicalC0Resolvent_positive hd ω lam Λ hΛ hω hSmooth α α.property f hf

/-- The spatial sub-Markov kernels represented by the physical C₀ evolution. -/
def gmpPhysicalC0KernelSemigroup {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) : MarkovProcess.SubMarkovKernelSemigroup (Vec d) :=
  (gmpPhysicalPositiveC0Resolvent hd ω lam Λ hΛ hω hSmooth).kernelSemigroup

/-- The physical spatial kernels represent the generated C₀ evolution. -/
theorem gmpPhysicalC0KernelSemigroup_integral {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0)
    (f : ZeroAtInftyContinuousMap (Vec d) ℝ) (x : Vec d) :
    ∫ y, f y ∂(gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x) =
      gmpPhysicalC0Semigroup hd ω lam Λ hΛ hω hSmooth t f x :=
  (gmpPhysicalPositiveC0Resolvent hd ω lam Λ hΛ hω hSmooth).integral_kernelSemigroup t f x

/-- The physical spatial kernels satisfy the Feller interface. -/
theorem gmpPhysicalC0KernelSemigroup_isFeller {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) :
    (gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth).IsFellerKernelSemigroup :=
  (gmpPhysicalPositiveC0Resolvent hd ω lam Λ hΛ hω hSmooth).isFellerKernelSemigroup_kernelSemigroup

/-- The Feller semigroup recovered from the physical kernels is the original C₀ evolution. -/
theorem gmpPhysicalC0KernelSemigroup_c0Semigroup {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) :
    (gmpPhysicalC0KernelSemigroup_isFeller hd ω lam Λ hΛ hω hSmooth).c0Semigroup =
      gmpPhysicalC0Semigroup hd ω lam Λ hΛ hω hSmooth :=
  (gmpPhysicalPositiveC0Resolvent hd ω lam Λ hΛ hω hSmooth).c0Semigroup_kernelSemigroup

/-- The physical L² evolution generated from the full source weighted-H¹ form. -/
def gmpPhysicalSemigroup {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    StronglyContinuousContractionSemigroup
      (Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :=
  (gmpPhysicalContractiveResolvent hd ω lam Λ hΛ hω).generatedSemigroup

/-- The generated physical evolution has exactly the original full-form resolvent. -/
theorem gmpPhysicalSemigroup_resolvent {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (α : PositiveShift) :
    (gmpPhysicalSemigroup hd ω lam Λ hΛ hω).resolvent α =
      gmpPhysicalResolvent hd ω lam Λ hΛ hω α α.property :=
  (gmpPhysicalContractiveResolvent hd ω lam Λ hΛ hω).resolvent_generatedSemigroup α

/-- The resolvent of the physical evolution satisfies the exact full-domain equation. -/
theorem gmpPhysicalSemigroup_isResolvent {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (α : PositiveShift) :
    SubdiffusiveProcess.DirichletForm.IsResolvent
      (gmpPhysicalClosedForm hd ω lam Λ hΛ hω) α
      ((gmpPhysicalSemigroup hd ω lam Λ hΛ hω).resolvent α) := by
  rw [gmpPhysicalSemigroup_resolvent]
  exact gmpPhysicalResolvent_isResolvent hd ω lam Λ hΛ hω α α.property

/-- Every generator-domain element belongs to the literal full weighted-H¹ domain. -/
theorem gmpPhysicalSemigroup_generator_physicalH1Member {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f : (gmpPhysicalSemigroup hd ω lam Λ hΛ hω).generatorDomain) :
    physicalH1Member ω hd lam f := by
  let R := gmpPhysicalContractiveResolvent hd ω lam Λ hΛ hω
  let α : PositiveShift := ⟨1, by norm_num [PositiveShift]⟩
  have hf : (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) ∈
      Set.range (R.operator α) := by
    rw [← R.generatorDomain_eq_range α]
    exact f.property
  obtain ⟨g, hg⟩ := hf
  rw [← hg]
  exact gmpPhysicalResolvent_physicalH1Member hd ω lam Λ hΛ hω α α.property g

/-- On its generator domain, the physical evolution has the full-form weak generator. -/
theorem gmpPhysicalSemigroup_generator_form {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f : (gmpPhysicalSemigroup hd ω lam Λ hΛ hω).generatorDomain)
    (v : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hv : v ∈ (gmpPhysicalClosedForm hd ω lam Λ hΛ hω).domain) :
    inner ℝ ((gmpPhysicalSemigroup hd ω lam Λ hΛ hω).generator f) v +
      (gmpPhysicalClosedForm hd ω lam Λ hΛ hω).form f v = 0 := by
  let α : PositiveShift := ⟨1, by norm_num [PositiveShift]⟩
  have hf := (gmpPhysicalSemigroup hd ω lam Λ hΛ hω).resolvent_smul_sub_generator α f
  rw [gmpPhysicalSemigroup_resolvent] at hf
  have he := (gmpPhysicalResolvent_isResolvent hd ω lam Λ hΛ hω α α.property).eq
    ((α : ℝ) • (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) -
      (gmpPhysicalSemigroup hd ω lam Λ hΛ hω).generator f) hv
  rw [hf, inner_sub_left, real_inner_smul_left] at he
  linarith only [he]

/-- On the generator domain, the semigroup difference quotients recover the full form. -/
theorem gmpPhysicalSemigroup_formLimit_generatorDomain {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f : (gmpPhysicalSemigroup hd ω lam Λ hΛ hω).generatorDomain) :
    Tendsto
      (fun t : ℝ≥0 => (t : ℝ)⁻¹ *
        inner ℝ ((f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) -
          (gmpPhysicalSemigroup hd ω lam Λ hΛ hω) t f) f)
      (𝓝[Set.Ioi 0] 0)
      (𝓝 ((gmpPhysicalClosedForm hd ω lam Λ hΛ hω).form f f)) := by
  have hf := gmpPhysicalSemigroup_generator_physicalH1Member hd ω lam Λ hΛ hω f
  have hform := gmpPhysicalSemigroup_generator_form hd ω lam Λ hΛ hω f f
    ((mem_gmpPhysicalClosedForm_domain_iff hd ω lam Λ hΛ hω f).mpr hf)
  have he : -inner ℝ ((gmpPhysicalSemigroup hd ω lam Λ hΛ hω).generator f) f =
      (gmpPhysicalClosedForm hd ω lam Λ hΛ hω).form f f := by
    linarith only [hform]
  have ht := ((gmpPhysicalSemigroup hd ω lam Λ hΛ hω).tendsto_generator' f).neg.inner
    (𝕜 := ℝ)
    (tendsto_const_nhds (x := (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))))
  simpa only [← smul_neg, neg_sub, real_inner_smul_left, inner_neg_left, he] using ht

/-- Symmetry of the full physical form passes to every time of its L² evolution. -/
theorem gmpPhysicalSemigroup_inner_comm {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (t : ℝ≥0)
    (f g : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    inner ℝ ((gmpPhysicalSemigroup hd ω lam Λ hΛ hω) t f) g =
      inner ℝ f ((gmpPhysicalSemigroup hd ω lam Λ hΛ hω) t g) := by
  let R := gmpPhysicalContractiveResolvent hd ω lam Λ hΛ hω
  have hR (α : PositiveShift) : IsSelfAdjoint (R.operator α) := by
    apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    intro u v
    change inner ℝ (gmpPhysicalResolvent hd ω lam Λ hΛ hω α α.property u) v = _
    rw [real_inner_comm]
    exact gmpPhysicalResolvent_inner_comm hd ω lam Λ hΛ hω α α.property v u
  have hY (α : PositiveShift) : IsSelfAdjoint (R.yosidaOperator α t) := by
    have hscaled := (IsSelfAdjoint.all (α : ℝ)).smul (hR α)
    have hgen := (IsSelfAdjoint.all (α : ℝ)).smul (hscaled.sub (IsSelfAdjoint.one _))
    exact ((IsSelfAdjoint.all (t : ℝ)).smul hgen).exp
  have he (n : ℕ) :
      inner ℝ (R.yosidaSemigroup (naturalShift n) t f) g =
        inner ℝ f (R.yosidaSemigroup (naturalShift n) t g) :=
    (hY (naturalShift n)).isSymmetric f g
  have hl := (R.tendsto_yosidaSemigroup_naturalShift_apply_generatedSemigroup t f).inner
    (𝕜 := ℝ)
    (tendsto_const_nhds (x := g))
  have hr := (tendsto_const_nhds (x := f)).inner (𝕜 := ℝ)
    (R.tendsto_yosidaSemigroup_naturalShift_apply_generatedSemigroup t g)
  simp_rw [he] at hl
  exact tendsto_nhds_unique hl hr

/-- The physical evolution preserves positivity in the original reversible measure. -/
theorem gmpPhysicalSemigroup_positive {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (t : ℝ≥0)
    {f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)}
    (hf : 0 ≤ᵐ[physicalReversibleMeasure ω hd lam] f) :
    0 ≤ᵐ[physicalReversibleMeasure ω hd lam]
      (gmpPhysicalSemigroup hd ω lam Λ hΛ hω) t f := by
  let R := gmpPhysicalContractiveResolvent hd ω lam Λ hΛ hω
  let C : Set (Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) := Set.Ici 0
  have hc : IsClosed C := isClosed_Ici
  have hv : Convex ℝ C := by
    intro u hu v hv a b ha hb hab
    apply (Lp.coeFn_nonneg _).mp
    filter_upwards [(Lp.coeFn_nonneg u).mpr hu, (Lp.coeFn_nonneg v).mpr hv,
      Lp.coeFn_smul a u, Lp.coeFn_smul b v, Lp.coeFn_add (a • u) (b • v)]
      with x hux hvx hau hbv hsum
    simpa only [hsum, Pi.add_apply, hau, hbv, Pi.smul_apply, smul_eq_mul,
      Pi.zero_apply] using add_nonneg (mul_nonneg ha hux) (mul_nonneg hb hvx)
  have hQ (α : PositiveShift) : PreservesSet (R.scaledOperator α) C C := by
    intro u hu
    apply (Lp.coeFn_nonneg _).mp
    have hp := gmpPhysicalResolvent_positive hd ω lam Λ hΛ hω α α.property
      ((Lp.coeFn_nonneg u).mpr hu)
    filter_upwards [hp, Lp.coeFn_smul (α : ℝ) (R.operator α u)] with x hx he
    change 0 ≤ ((α : ℝ) • R.operator α u) x
    rw [he, Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg α.property.le hx
  exact (Lp.coeFn_nonneg _).mpr
    (R.preservesSet_generatedSemigroup_of_scaledOperator C hc hv
      (by change (0 : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) ≤ 0; exact le_rfl) hQ t
      ((Lp.coeFn_nonneg f).mp hf))

/-- The physical evolution is submarkovian on actual L² data between zero and one. -/
theorem gmpPhysicalSemigroup_submarkov {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (t : ℝ≥0)
    {f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)}
    (hf0 : 0 ≤ᵐ[physicalReversibleMeasure ω hd lam] f)
    (hf1 : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, f x ≤ 1) :
    ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      0 ≤ (gmpPhysicalSemigroup hd ω lam Λ hΛ hω) t f x ∧
        (gmpPhysicalSemigroup hd ω lam Λ hΛ hω) t f x ≤ 1 := by
  let R := gmpPhysicalContractiveResolvent hd ω lam Λ hΛ hω
  let C : Set (Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :=
    {u | ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, 0 ≤ u x ∧ u x ≤ 1}
  have hc : IsClosed C := IsSeqClosed.isClosed <| by
    intro fs u hfs hlim
    obtain ⟨φ, -, hφ⟩ :=
      tendstoInMeasure_of_tendsto_Lp hlim |>.exists_seq_tendsto_ae
    filter_upwards [countable_iInter_mem.mpr hfs, hφ] with x hx hφx
    exact ⟨ge_of_tendsto' hφx (fun n => (Set.mem_iInter.mp hx (φ n)).1),
      le_of_tendsto' hφx (fun n => (Set.mem_iInter.mp hx (φ n)).2)⟩
  have hv : Convex ℝ C := by
    intro u hu v hv a b ha hb hab
    filter_upwards [hu, hv, Lp.coeFn_smul a u, Lp.coeFn_smul b v,
      Lp.coeFn_add (a • u) (b • v)] with x hux hvx hau hbv hsum
    simp only [hsum, Pi.add_apply, hau, hbv, Pi.smul_apply, smul_eq_mul]
    refine ⟨add_nonneg (mul_nonneg ha hux.1) (mul_nonneg hb hvx.1), ?_⟩
    calc
      a * u x + b * v x ≤ a * 1 + b * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left hux.2 ha)
          (mul_le_mul_of_nonneg_left hvx.2 hb)
      _ = 1 := by simpa only [mul_one] using hab
  have hzero : (0 : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) ∈ C := by
    filter_upwards [Lp.coeFn_zero ℝ 2 (physicalReversibleMeasure ω hd lam)] with x hx
    simp only [hx, Pi.zero_apply, le_refl, zero_le_one, and_self]
  have hQ (α : PositiveShift) : PreservesSet (R.scaledOperator α) C C := by
    intro u hu
    change ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, 0 ≤ u x ∧ u x ≤ 1 at hu
    have hp := gmpPhysicalResolvent_submarkov hd ω lam Λ hΛ hω α α.property
      (hu.mono fun _ hx => hx.1) (hu.mono fun _ hx => hx.2)
    filter_upwards [hp, Lp.coeFn_smul (α : ℝ) (R.operator α u)] with x hx he
    change 0 ≤ ((α : ℝ) • R.operator α u) x ∧
      ((α : ℝ) • R.operator α u) x ≤ 1
    rw [he, Pi.smul_apply, smul_eq_mul]
    exact hx
  exact R.preservesSet_generatedSemigroup_of_scaledOperator C hc hv hzero hQ t
    (hf0.and hf1)

/-- A compactly supported continuous physical observable as a C₀ function. -/
def gmpPhysicalCompactC0 {d : ℕ} (φ : Vec d → ℝ) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) : ZeroAtInftyContinuousMap (Vec d) ℝ :=
  ⟨EinsteinFull.Work.W5.gantertCompactObservable φ hφ hc, hc.is_zero_at_infty⟩

/-- The C₀ resolvent inverts the actual physical generator on smooth compact tests. -/
theorem gmpPhysicalC0Resolvent_compactTest {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (α : ℝ) (hα : 0 < α)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    let u := gmpPhysicalCompactC0 φ hφ.continuous hc
    let Lφ := physicalGenerator (firstCoordinateIndex hd) ω lam φ
    let v := gmpPhysicalCompactC0 Lφ
      (EinsteinFull.Work.W5.gantert_contDiff_physicalGenerator _ ω hSmooth lam hφ).continuous
      (EinsteinFull.Work.W5.gantert_hasCompactSupport_physicalGenerator _ ω lam hc)
    gmpPhysicalC0Resolvent hd ω lam Λ hΛ hω hSmooth α hα (α • u - v) = u := by
  dsimp only
  let u := gmpPhysicalCompactC0 φ hφ.continuous hc
  let v := gmpPhysicalCompactC0 (physicalGenerator (firstCoordinateIndex hd) ω lam φ)
    (EinsteinFull.Work.W5.gantert_contDiff_physicalGenerator _ ω hSmooth lam hφ).continuous
    (EinsteinFull.Work.W5.gantert_hasCompactSupport_physicalGenerator _ ω lam hc)
  let U := gmpPhysicalH1Value hd ω lam Λ hω
    (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hc)
  let V := EinsteinFull.C8GMP.compactTestGeneratorL2 hd ω hSmooth lam φ hφ hc
  have hu : (U : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] u :=
    gmpPhysicalCompactTest_value_ae hd ω lam Λ hω φ hφ hc
  have hv : (V : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] v :=
    gmpPhysicalCompactTestGenerator_ae hd ω hSmooth lam φ hφ hc
  have hinput : ((α • U - V : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) : Vec d → ℝ) =ᵐ[
      physicalReversibleMeasure ω hd lam] (α • u - v : ZeroAtInftyContinuousMap (Vec d) ℝ) := by
    filter_upwards [hu, hv, Lp.coeFn_smul α U, Lp.coeFn_sub (α • U) V] with x hx hy hs hsub
    change (α • U - V) x = α * u x - v x
    rw [hsub]
    change (α • U) x - V x = α * u x - v x
    rw [hs]
    change α * U x - V x = α * u x - v x
    rw [hx, hy]
  have hres := gmpPhysicalC0Resolvent_ae_of_memLp hd ω lam Λ hΛ hω hSmooth α hα
    (α • u - v) (α • U - V) hinput
  have hinv : gmpPhysicalResolvent hd ω lam Λ hΛ hω α hα (α • U - V) = U :=
    gmpPhysicalResolvent_compactTest hd ω lam Λ hΛ hω hSmooth α hα φ hφ hc
  rw [hinv] at hres
  have heq := hres.trans hu
  ext x
  exact congrFun (gmpPhysical_continuousRepresentative_unique hd ω lam
    (gmpPhysicalC0Resolvent hd ω lam Λ hΛ hω hSmooth α hα (α • u - v)).continuous
    u.continuous heq) x

/-- Smooth compact tests belong to the physical C₀ generator domain. -/
theorem gmpPhysicalC0Semigroup_compactTest_mem_generatorDomain {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    gmpPhysicalCompactC0 φ hφ.continuous hc ∈
      (gmpPhysicalC0Semigroup hd ω lam Λ hΛ hω hSmooth).generatorDomain := by
  let R := gmpPhysicalC0ContractiveResolvent hd ω lam Λ hΛ hω hSmooth
  let α : PositiveShift := ⟨1, by norm_num [PositiveShift]⟩
  change _ ∈ (R.generatedSemigroup.generatorDomain : Set (ZeroAtInftyContinuousMap (Vec d) ℝ))
  rw [R.generatorDomain_eq_range α]
  exact ⟨_, gmpPhysicalC0Resolvent_compactTest hd ω lam Λ hΛ hω hSmooth
    α α.property φ hφ hc⟩

/-- The physical C₀ generator equals the literal differential operator on smooth compact tests. -/
theorem gmpPhysicalC0Semigroup_generator_compactTest {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    (gmpPhysicalC0Semigroup hd ω lam Λ hΛ hω hSmooth).generator
      ⟨gmpPhysicalCompactC0 φ hφ.continuous hc,
        gmpPhysicalC0Semigroup_compactTest_mem_generatorDomain hd ω lam Λ hΛ hω
          hSmooth φ hφ hc⟩ =
      gmpPhysicalCompactC0 (physicalGenerator (firstCoordinateIndex hd) ω lam φ)
        (EinsteinFull.Work.W5.gantert_contDiff_physicalGenerator _ ω hSmooth lam hφ).continuous
        (EinsteinFull.Work.W5.gantert_hasCompactSupport_physicalGenerator _ ω lam hc) := by
  let R := gmpPhysicalC0ContractiveResolvent hd ω lam Λ hΛ hω hSmooth
  let α : PositiveShift := ⟨1, by norm_num [PositiveShift]⟩
  calc
    _ = (α : ℝ) • gmpPhysicalCompactC0 φ hφ.continuous hc -
        ((α : ℝ) • gmpPhysicalCompactC0 φ hφ.continuous hc -
          gmpPhysicalCompactC0 (physicalGenerator (firstCoordinateIndex hd) ω lam φ)
            (EinsteinFull.Work.W5.gantert_contDiff_physicalGenerator _ ω hSmooth lam hφ).continuous
            (EinsteinFull.Work.W5.gantert_hasCompactSupport_physicalGenerator _ ω lam hc)) :=
      R.generator_apply_of_operator_eq α
        (gmpPhysicalC0Semigroup_compactTest_mem_generatorDomain hd ω lam Λ hΛ hω
          hSmooth φ hφ hc)
        (gmpPhysicalC0Resolvent_compactTest hd ω lam Λ hΛ hω hSmooth
          α α.property φ hφ hc)
    _ = _ := sub_sub_cancel _ _

/-- Every compact smooth test is in the generator domain of the physical evolution. -/
theorem gmpPhysicalSemigroup_compactTest_mem_generatorDomain {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    gmpPhysicalH1Value hd ω lam Λ hω
      (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hc) ∈
        (gmpPhysicalSemigroup hd ω lam Λ hΛ hω).generatorDomain := by
  let R := gmpPhysicalContractiveResolvent hd ω lam Λ hΛ hω
  let α : PositiveShift := ⟨1, by norm_num [PositiveShift]⟩
  change _ ∈ (R.generatedSemigroup.generatorDomain :
    Set (Lp ℝ 2 (physicalReversibleMeasure ω hd lam)))
  rw [R.generatorDomain_eq_range α]
  exact ⟨_, gmpPhysicalResolvent_compactTest hd ω lam Λ hΛ hω hSmooth
    α α.property φ hφ hc⟩

/-- On compact smooth tests the generated operator is the literal physical generator. -/
theorem gmpPhysicalSemigroup_generator_compactTest {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    (gmpPhysicalSemigroup hd ω lam Λ hΛ hω).generator
      ⟨gmpPhysicalH1Value hd ω lam Λ hω
        (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hc),
        gmpPhysicalSemigroup_compactTest_mem_generatorDomain hd ω lam Λ hΛ hω
          hSmooth φ hφ hc⟩ =
      EinsteinFull.C8GMP.compactTestGeneratorL2 hd ω hSmooth lam φ hφ hc := by
  let R := gmpPhysicalContractiveResolvent hd ω lam Λ hΛ hω
  let α : PositiveShift := ⟨1, by norm_num [PositiveShift]⟩
  calc
    _ = (α : ℝ) • gmpPhysicalH1Value hd ω lam Λ hω
        (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hc) -
        ((α : ℝ) • gmpPhysicalH1Value hd ω lam Λ hω
          (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hc) -
          EinsteinFull.C8GMP.compactTestGeneratorL2 hd ω hSmooth lam φ hφ hc) :=
      R.generator_apply_of_operator_eq α
        (gmpPhysicalSemigroup_compactTest_mem_generatorDomain hd ω lam Λ hΛ hω
          hSmooth φ hφ hc)
        (gmpPhysicalResolvent_compactTest hd ω lam Λ hΛ hω hSmooth
          α α.property φ hφ hc)
    _ = _ := sub_sub_cancel _ _

/-- Along a generator-domain orbit, energy is the generator pairing. -/
theorem gmpPhysicalSemigroup_orbit_energy_generator {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f : (gmpPhysicalSemigroup hd ω lam Λ hΛ hω).generatorDomain) (t : ℝ≥0) :
    let S := gmpPhysicalSemigroup hd ω lam Λ hΛ hω
    (gmpPhysicalClosedForm hd ω lam Λ hΛ hω).form (S t f) (S t f) =
      -inner ℝ (S t (S.generator f)) (S t f) := by
  let S := gmpPhysicalSemigroup hd ω lam Λ hΛ hω
  let g : S.generatorDomain := ⟨S t f, S.operator_mem_generatorDomain f t⟩
  have hg := gmpPhysicalSemigroup_generator_physicalH1Member hd ω lam Λ hΛ hω g
  have h := gmpPhysicalSemigroup_generator_form hd ω lam Λ hΛ hω g g
    ((mem_gmpPhysicalClosedForm_domain_iff hd ω lam Λ hΛ hω g).mpr hg)
  change inner ℝ (S.generator g) (S t f) + _ = 0 at h
  rw [S.generator_operator] at h
  linarith only [h]

/-- The energy of a generator-domain orbit is continuous in real time. -/
theorem gmpPhysicalSemigroup_continuous_orbit_energy {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f : (gmpPhysicalSemigroup hd ω lam Λ hΛ hω).generatorDomain) :
    let S := gmpPhysicalSemigroup hd ω lam Λ hΛ hω
    Continuous (fun s : ℝ => (gmpPhysicalClosedForm hd ω lam Λ hΛ hω).form
      (S (Real.toNNReal s) f) (S (Real.toNNReal s) f)) := by
  let S := gmpPhysicalSemigroup hd ω lam Λ hΛ hω
  have hc : Continuous (fun s : ℝ => -inner ℝ
      (S (Real.toNNReal s) (S.generator f)) (S (Real.toNNReal s) f)) :=
    ((S.continuous_operator_toNNReal (S.generator f)).inner
      (S.continuous_operator_toNNReal f)).neg
  convert hc using 1
  funext s
  exact (gmpPhysicalSemigroup_orbit_energy_generator hd ω lam Λ hΛ hω f
    (Real.toNNReal s))

/-- The full physical weighted-H¹ domain is invariant, and its energy decreases. -/
theorem gmpPhysicalSemigroup_energy_le {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (t : ℝ≥0)
    {f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)}
    (hf : physicalH1Member ω hd lam f) :
    physicalH1Member ω hd lam ((gmpPhysicalSemigroup hd ω lam Λ hΛ hω) t f) ∧
      (gmpPhysicalClosedForm hd ω lam Λ hΛ hω).form
        ((gmpPhysicalSemigroup hd ω lam Λ hΛ hω) t f)
        ((gmpPhysicalSemigroup hd ω lam Λ hΛ hω) t f) ≤
      (gmpPhysicalClosedForm hd ω lam Λ hΛ hω).form f f := by
  let E := gmpPhysicalClosedForm hd ω lam Λ hΛ hω
  let R := gmpPhysicalContractiveResolvent hd ω lam Λ hΛ hω
  have hfE : f ∈ E.domain :=
    (mem_gmpPhysicalClosedForm_domain_iff hd ω lam Λ hΛ hω f).mpr hf
  let C : Set (Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :=
    {u | u ∈ E.domain ∧ E.form u u ≤ E.form f f}
  have hc : IsClosed C := closedForm_energySublevel_isClosed E (E.form f f)
  have hv : Convex ℝ C := closedForm_energySublevel_convex E (E.form f f)
  have hz : (0 : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) ∈ C := by
    exact ⟨E.domain.zero_mem, (E.form_zero_left E.domain.zero_mem).trans_le
      (E.form_nonneg f hfE)⟩
  have hQ (α : PositiveShift) : PreservesSet (R.scaledOperator α) C C := by
    intro u hu
    have hg := (gmpPhysicalResolvent_isResolvent hd ω lam Λ hΛ hω α α.property).mem_domain u
    have hb := SubdiffusiveProcess.DirichletForm.FOTConstruction.scaled_resolvent_energy_bound
      (gmpPhysicalDirichletForm hd ω lam Λ hΛ hω) α.property
      (gmpPhysicalResolvent_isResolvent hd ω lam Λ hΛ hω α α.property) hu.1
    refine ⟨E.domain.smul_mem (α : ℝ) hg, ?_⟩
    exact (le_add_of_nonneg_right (mul_nonneg α.property.le (sq_nonneg _))).trans
      (hb.trans hu.2)
  have ht := R.preservesSet_generatedSemigroup_of_scaledOperator C hc hv hz hQ t
    (show f ∈ C from ⟨hfE, le_rfl⟩)
  exact ⟨(mem_gmpPhysicalClosedForm_domain_iff hd ω lam Λ hΛ hω _).mp ht.1, ht.2⟩

/-- Energy at twice a time is bounded by the energy at that time. -/
theorem gmpPhysicalSemigroup_orbit_energy_double_le {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f : (gmpPhysicalSemigroup hd ω lam Λ hΛ hω).generatorDomain) (t : ℝ≥0) :
    let S := gmpPhysicalSemigroup hd ω lam Λ hΛ hω
    let E := gmpPhysicalClosedForm hd ω lam Λ hΛ hω
    E.form (S (t + t) f) (S (t + t) f) ≤ E.form (S t f) (S t f) := by
  let S := gmpPhysicalSemigroup hd ω lam Λ hΛ hω
  have hf := gmpPhysicalSemigroup_generator_physicalH1Member hd ω lam Λ hΛ hω f
  have ht := gmpPhysicalSemigroup_energy_le hd ω lam Λ hΛ hω t
    (gmpPhysicalSemigroup_energy_le hd ω lam Λ hΛ hω t hf).1
  change (gmpPhysicalClosedForm hd ω lam Λ hΛ hω).form (S (t + t) f) (S (t + t) f) ≤ _
  rw [S.add_apply]
  exact ht.2

/-- The generator graph is exactly the weak operator of the full physical form. -/
theorem gmpPhysicalSemigroup_generator_iff {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f g : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    (∃ hf : f ∈ (gmpPhysicalSemigroup hd ω lam Λ hΛ hω).generatorDomain,
      (gmpPhysicalSemigroup hd ω lam Λ hΛ hω).generator ⟨f, hf⟩ = g) ↔
    physicalH1Member ω hd lam f ∧
      ∀ v ∈ (gmpPhysicalClosedForm hd ω lam Λ hΛ hω).domain,
        inner ℝ g v + (gmpPhysicalClosedForm hd ω lam Λ hΛ hω).form f v = 0 := by
  constructor
  · rintro ⟨hf, rfl⟩
    exact ⟨gmpPhysicalSemigroup_generator_physicalH1Member hd ω lam Λ hΛ hω ⟨f, hf⟩,
      fun v hv => gmpPhysicalSemigroup_generator_form hd ω lam Λ hΛ hω ⟨f, hf⟩ v hv⟩
  · rintro ⟨hf, hform⟩
    let R := gmpPhysicalContractiveResolvent hd ω lam Λ hΛ hω
    let α : PositiveShift := ⟨1, by norm_num [PositiveShift]⟩
    have he : R.operator α ((α : ℝ) • f - g) = f := by
      symm
      apply gmpPhysicalResolvent_unique hd ω lam Λ hΛ hω α α.property _ hf
      intro v hv
      have h := hform v hv
      rw [inner_sub_left, real_inner_smul_left]
      change _ + (gmpPhysicalClosedForm hd ω lam Λ hΛ hω).form f v = _
      linarith only [h]
    have hdom : f ∈ (gmpPhysicalSemigroup hd ω lam Λ hΛ hω).generatorDomain := by
      change f ∈ (R.generatedSemigroup.generatorDomain :
        Set (Lp ℝ 2 (physicalReversibleMeasure ω hd lam)))
      rw [R.generatorDomain_eq_range α]
      exact ⟨_, he⟩
    refine ⟨hdom, ?_⟩
    calc
      _ = (α : ℝ) • f - ((α : ℝ) • f - g) :=
        R.generator_apply_of_operator_eq α hdom he
      _ = g := sub_sub_cancel _ _

/-- Full weighted-H¹ data are continuous at time zero in the physical energy norm. -/
theorem gmpPhysicalSemigroup_tendsto_energyNormSq_zero {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    {f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)}
    (hf : physicalH1Member ω hd lam f) :
    Tendsto (fun t : ℝ≥0 => (gmpPhysicalClosedForm hd ω lam Λ hΛ hω).energyNormSq
      ((gmpPhysicalSemigroup hd ω lam Λ hΛ hω) t f - f)) (𝓝 0) (𝓝 0) := by
  let E := gmpPhysicalClosedForm hd ω lam Λ hΛ hω
  apply tendsto_nhds_iff_seq_tendsto.mpr
  intro ts hts
  have hu := fun n => gmpPhysicalSemigroup_energy_le hd ω lam Λ hΛ hω (ts n) hf
  apply SubdiffusiveProcess.DirichletForm.FOTConstruction.energy_tendsto_of_limsup_le E
    (fun n => (mem_gmpPhysicalClosedForm_domain_iff hd ω lam Λ hΛ hω _).mpr (hu n).1)
    ((mem_gmpPhysicalClosedForm_domain_iff hd ω lam Λ hΛ hω f).mpr hf)
  · have ht := ((gmpPhysicalSemigroup hd ω lam Λ hΛ hω).continuous_orbit f).tendsto 0
    simpa only [StronglyContinuousContractionSemigroup.zero_apply, Function.comp_def] using
      ht.comp hts
  · intro ε hε
    exact Eventually.of_forall fun n => (hu n).2.trans (le_add_of_nonneg_right hε.le)

/-- A time average stays in the same closed full-domain energy sublevel. -/
theorem gmpPhysicalSemigroup_orbitAverage_energy_le {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    {f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)}
    (hf : physicalH1Member ω hd lam f) (t : ℝ≥0) :
    let u := (t : ℝ)⁻¹ • (gmpPhysicalSemigroup hd ω lam Λ hΛ hω).orbitIntegral f t
    u ∈ (gmpPhysicalClosedForm hd ω lam Λ hΛ hω).domain ∧
      (gmpPhysicalClosedForm hd ω lam Λ hΛ hω).form u u ≤
        (gmpPhysicalClosedForm hd ω lam Λ hΛ hω).form f f := by
  let E := gmpPhysicalClosedForm hd ω lam Λ hΛ hω
  let S := gmpPhysicalSemigroup hd ω lam Λ hΛ hω
  have hfE : f ∈ E.domain :=
    (mem_gmpPhysicalClosedForm_domain_iff hd ω lam Λ hΛ hω f).mpr hf
  by_cases ht : t = 0
  · subst t
    simpa only [NNReal.coe_zero, inv_zero, zero_smul] using
      (show (0 : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) ∈ E.domain ∧
        E.form 0 0 ≤ E.form f f from
        ⟨E.domain.zero_mem, (E.form_zero_left E.domain.zero_mem).trans_le
          (E.form_nonneg f hfE)⟩)
  have htpos : 0 < (t : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ht)
  have hμ0 : (volume : Measure ℝ) (Set.uIoc (0 : ℝ) (t : ℝ)) ≠ 0 := by
    rw [Real.volume_uIoc, sub_zero, abs_of_nonneg t.coe_nonneg]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr htpos)
  have hμtop : (volume : Measure ℝ) (Set.uIoc (0 : ℝ) (t : ℝ)) ≠ ∞ := by
    rw [Real.volume_uIoc]
    exact ENNReal.ofReal_ne_top
  have hav := (closedForm_energySublevel_convex E (E.form f f)).set_average_mem
    (closedForm_energySublevel_isClosed E (E.form f f)) hμ0 hμtop
    (Eventually.of_forall fun s : ℝ => by
      have hs := gmpPhysicalSemigroup_energy_le hd ω lam Λ hΛ hω (Real.toNNReal s) hf
      exact ⟨(mem_gmpPhysicalClosedForm_domain_iff hd ω lam Λ hΛ hω _).mpr hs.1, hs.2⟩)
    ((S.continuous_operator_toNNReal f).intervalIntegrable 0 t).def'
  rw [interval_average_eq, sub_zero] at hav
  exact hav

/-- The energy of a generator-domain orbit average obeys Jensen's inequality. -/
theorem gmpPhysicalSemigroup_orbitAverage_energy_le_integral {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f : (gmpPhysicalSemigroup hd ω lam Λ hΛ hω).generatorDomain)
    (t : ℝ≥0) (ht : 0 < t) :
    let S := gmpPhysicalSemigroup hd ω lam Λ hΛ hω
    let E := gmpPhysicalClosedForm hd ω lam Λ hΛ hω
    E.form ((t : ℝ)⁻¹ • S.orbitIntegral f t) ((t : ℝ)⁻¹ • S.orbitIntegral f t) ≤
      (t : ℝ)⁻¹ * ∫ s in (0 : ℝ)..t,
        E.form (S (Real.toNNReal s) f) (S (Real.toNNReal s) f) := by
  let S := gmpPhysicalSemigroup hd ω lam Λ hΛ hω
  let E := gmpPhysicalClosedForm hd ω lam Λ hΛ hω
  have htpos : 0 < (t : ℝ) := NNReal.coe_pos.mpr ht
  have hμ0 : (volume : Measure ℝ) (Set.uIoc (0 : ℝ) (t : ℝ)) ≠ 0 := by
    rw [Real.volume_uIoc, sub_zero, abs_of_nonneg t.coe_nonneg]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr htpos)
  have hμtop : (volume : Measure ℝ) (Set.uIoc (0 : ℝ) (t : ℝ)) ≠ ∞ := by
    rw [Real.volume_uIoc]
    exact ENNReal.ofReal_ne_top
  have hf := gmpPhysicalSemigroup_generator_physicalH1Member hd ω lam Λ hΛ hω f
  have h := closedForm_energy_setAverage_le E hμ0 hμtop
    (fun s : ℝ => S (Real.toNNReal s) f)
    ((S.continuous_operator_toNNReal f).intervalIntegrable 0 t).def'
    ((gmpPhysicalSemigroup_continuous_orbit_energy hd ω lam Λ hΛ hω f).intervalIntegrable
      0 t).def'
    (Eventually.of_forall fun s : ℝ =>
      (mem_gmpPhysicalClosedForm_domain_iff hd ω lam Λ hΛ hω _).mpr
        (gmpPhysicalSemigroup_energy_le hd ω lam Λ hΛ hω (Real.toNNReal s) hf).1)
  rw [interval_average_eq, sub_zero, interval_average_eq, sub_zero] at h
  change E.form ((t : ℝ)⁻¹ • S.orbitIntegral f t) ((t : ℝ)⁻¹ • S.orbitIntegral f t) ≤ _
  rw [S.orbitIntegral_apply]
  simpa only [smul_eq_mul] using h.2

/-- The orbit average has the required difference-quotient bound on the generator domain. -/
theorem gmpPhysicalSemigroup_orbitAverage_energy_le_differenceQuotient_generator
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f : (gmpPhysicalSemigroup hd ω lam Λ hΛ hω).generatorDomain)
    (t : ℝ≥0) (ht : 0 < t) :
    let S := gmpPhysicalSemigroup hd ω lam Λ hΛ hω
    let E := gmpPhysicalClosedForm hd ω lam Λ hΛ hω
    E.form ((t : ℝ)⁻¹ • S.orbitIntegral f t) ((t : ℝ)⁻¹ • S.orbitIntegral f t) ≤
      (t : ℝ)⁻¹ * inner ℝ ((f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) - S t f) f := by
  let S := gmpPhysicalSemigroup hd ω lam Λ hΛ hω
  let E := gmpPhysicalClosedForm hd ω lam Λ hΛ hω
  have hpoint (s : ℝ) : E.form (S (Real.toNNReal s) f) (S (Real.toNNReal s) f) ≤
      -inner ℝ (S (Real.toNNReal s) (S.generator f)) f := by
    let q := Real.toNNReal s
    have hhalf : q / 2 + q / 2 = q := by
      ext
      simp
    have hb := gmpPhysicalSemigroup_orbit_energy_double_le hd ω lam Λ hΛ hω f (q / 2)
    change E.form (S (q / 2 + q / 2) f) (S (q / 2 + q / 2) f) ≤
      E.form (S (q / 2) f) (S (q / 2) f) at hb
    rw [hhalf] at hb
    have he := gmpPhysicalSemigroup_orbit_energy_generator hd ω lam Λ hΛ hω f (q / 2)
    change E.form (S (q / 2) f) (S (q / 2) f) =
      -inner ℝ (S (q / 2) (S.generator f)) (S (q / 2) f) at he
    rw [gmpPhysicalSemigroup_inner_comm hd ω lam Λ hΛ hω (q / 2)
      (S.generator f) (S (q / 2) f), ← S.add_apply, hhalf,
      ← gmpPhysicalSemigroup_inner_comm hd ω lam Λ hΛ hω q (S.generator f) f] at he
    exact hb.trans_eq he
  have hcont : Continuous (fun s : ℝ =>
      -inner ℝ (S (Real.toNNReal s) (S.generator f)) f) :=
    ((S.continuous_operator_toNNReal (S.generator f)).inner continuous_const).neg
  have hint := intervalIntegral.integral_mono_on (μ := volume) t.coe_nonneg
    ((gmpPhysicalSemigroup_continuous_orbit_energy hd ω lam Λ hΛ hω f).intervalIntegrable 0 t)
    (hcont.intervalIntegrable 0 t) (fun s _ => hpoint s)
  have hcor : (∫ s in (0 : ℝ)..t, -inner ℝ (S (Real.toNNReal s) (S.generator f)) f) =
      inner ℝ ((f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) - S t f) f := by
    rw [intervalIntegral.integral_neg]
    have hi := (innerSL ℝ (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))).intervalIntegral_comp_comm (μ := volume)
      ((S.continuous_operator_toNNReal (S.generator f)).intervalIntegrable 0 t)
    simp only [innerSL_apply_apply] at hi
    have hswap : (∫ s in (0 : ℝ)..t, inner ℝ (S (Real.toNNReal s) (S.generator f))
        (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))) =
        ∫ s in (0 : ℝ)..t, inner ℝ (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
          (S (Real.toNNReal s) (S.generator f)) := by
      apply intervalIntegral.integral_congr
      intro s _
      exact real_inner_comm _ _
    rw [hswap, hi, ← S.operator_sub_eq_integral f t]
    rw [inner_sub_right, inner_sub_left,
      real_inner_comm (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) (S t f)]
    ring
  calc
    _ ≤ (t : ℝ)⁻¹ * ∫ s in (0 : ℝ)..t,
        E.form (S (Real.toNNReal s) f) (S (Real.toNNReal s) f) :=
      gmpPhysicalSemigroup_orbitAverage_energy_le_integral hd ω lam Λ hΛ hω f t ht
    _ ≤ (t : ℝ)⁻¹ * ∫ s in (0 : ℝ)..t,
        -inner ℝ (S (Real.toNNReal s) (S.generator f)) f :=
      mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr t.coe_nonneg)
    _ = _ := by rw [hcor]

/-- The orbit average energy is bounded by the difference quotient for all L² inputs. -/
theorem gmpPhysicalSemigroup_orbitAverage_energy_le_differenceQuotient
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (t : ℝ≥0) (ht : 0 < t) :
    let S := gmpPhysicalSemigroup hd ω lam Λ hΛ hω
    (gmpPhysicalClosedForm hd ω lam Λ hΛ hω).form
      ((t : ℝ)⁻¹ • S.orbitIntegral f t) ((t : ℝ)⁻¹ • S.orbitIntegral f t) ≤
      (t : ℝ)⁻¹ * inner ℝ (f - S t f) f := by
  let S := gmpPhysicalSemigroup hd ω lam Λ hΛ hω
  let E := gmpPhysicalClosedForm hd ω lam Λ hΛ hω
  let a (r : ℝ≥0) : S.generatorDomain :=
    ⟨(r : ℝ)⁻¹ • S.orbitIntegral f r,
      S.generatorDomain.smul_mem _ (S.orbitIntegral_mem_generatorDomain f r)⟩
  have ha : Tendsto (fun r : ℝ≥0 => (a r : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)))
      (𝓝[Set.Ioi 0] 0) (𝓝 f) := S.tendsto_inv_smul_orbitIntegral f
  have hv := (S.tendsto_orbitIntegral ha t).const_smul ((t : ℝ)⁻¹)
  have hs := ((S t).continuous.tendsto f).comp ha
  have hq := ((ha.sub hs).inner (𝕜 := ℝ) ha).const_mul ((t : ℝ)⁻¹)
  have hp := hv.prodMk_nhds hq
  have hm := (closedForm_energyEpigraph_isClosed E).mem_of_tendsto hp
    (Eventually.of_forall fun r => by
      have hdI := S.orbitIntegral_mem_generatorDomain (a r) t
      have hdE : S.orbitIntegral (a r) t ∈ E.domain :=
        (mem_gmpPhysicalClosedForm_domain_iff hd ω lam Λ hΛ hω _).mpr
          (gmpPhysicalSemigroup_generator_physicalH1Member hd ω lam Λ hΛ hω ⟨_, hdI⟩)
      exact ⟨E.domain.smul_mem _ hdE,
        gmpPhysicalSemigroup_orbitAverage_energy_le_differenceQuotient_generator
          hd ω lam Λ hΛ hω (a r) t ht⟩)
  exact hm.2

/-- Orbit averages approximate every full-domain datum in the physical energy norm. -/
theorem gmpPhysicalSemigroup_tendsto_orbitAverage_energyNormSq {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    {f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)}
    (hf : physicalH1Member ω hd lam f) :
    Tendsto (fun t : ℝ≥0 => (gmpPhysicalClosedForm hd ω lam Λ hΛ hω).energyNormSq
      ((t : ℝ)⁻¹ • (gmpPhysicalSemigroup hd ω lam Λ hΛ hω).orbitIntegral f t - f))
      (𝓝[Set.Ioi 0] 0) (𝓝 0) := by
  let E := gmpPhysicalClosedForm hd ω lam Λ hΛ hω
  apply Filter.tendsto_iff_seq_tendsto.mpr
  intro ts hts
  have hu := fun n => gmpPhysicalSemigroup_orbitAverage_energy_le hd ω lam Λ hΛ hω hf (ts n)
  apply SubdiffusiveProcess.DirichletForm.FOTConstruction.energy_tendsto_of_limsup_le E
    (fun n => (hu n).1)
    ((mem_gmpPhysicalClosedForm_domain_iff hd ω lam Λ hΛ hω f).mpr hf)
  · exact ((gmpPhysicalSemigroup hd ω lam Λ hΛ hω).tendsto_inv_smul_orbitIntegral f).comp hts
  · intro ε hε
    exact Eventually.of_forall fun n => (hu n).2.trans (le_add_of_nonneg_right hε.le)

/-- The difference quotients recover the physical form on its entire weighted-H¹ domain. -/
theorem gmpPhysicalSemigroup_formLimit {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    {f v : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)}
    (hf : physicalH1Member ω hd lam f) (hv : physicalH1Member ω hd lam v) :
    Tendsto
      (fun t : ℝ≥0 => (t : ℝ)⁻¹ *
        inner ℝ (f - (gmpPhysicalSemigroup hd ω lam Λ hΛ hω) t f) v)
      (𝓝[Set.Ioi 0] 0)
      (𝓝 ((gmpPhysicalClosedForm hd ω lam Λ hΛ hω).form f v)) := by
  let E := gmpPhysicalClosedForm hd ω lam Λ hΛ hω
  let S := gmpPhysicalSemigroup hd ω lam Λ hΛ hω
  have hvE : v ∈ E.domain :=
    (mem_gmpPhysicalClosedForm_domain_iff hd ω lam Λ hΛ hω v).mpr hv
  have he (t : ℝ≥0) :
      (t : ℝ)⁻¹ * inner ℝ (f - S t f) v =
        E.form ((t : ℝ)⁻¹ • S.orbitIntegral f t) v := by
    have hdI := S.orbitIntegral_mem_generatorDomain f t
    have hform := gmpPhysicalSemigroup_generator_form hd ω lam Λ hΛ hω
      ⟨S.orbitIntegral f t, hdI⟩ v hvE
    rw [S.generator_orbitIntegral, inner_sub_left] at hform
    rw [E.form_smul_left (t : ℝ)⁻¹ (S.orbitIntegral f t)
      (gmpPhysicalSemigroup_generator_physicalH1Member hd ω lam Λ hΛ hω
        ⟨S.orbitIntegral f t, hdI⟩ |>
        (mem_gmpPhysicalClosedForm_domain_iff hd ω lam Λ hΛ hω _).mpr) v hvE,
      inner_sub_left]
    linear_combination -(t : ℝ)⁻¹ * hform
  apply Filter.tendsto_iff_seq_tendsto.mpr
  intro ts hts
  have hu := fun n => gmpPhysicalSemigroup_orbitAverage_energy_le hd ω lam Λ hΛ hω hf (ts n)
  have hlim := E.tendsto_form_of_tendsto_energyNormSq (fun n => (hu n).1)
    ((mem_gmpPhysicalClosedForm_domain_iff hd ω lam Λ hΛ hω f).mpr hf) hvE
    ((gmpPhysicalSemigroup_tendsto_orbitAverage_energyNormSq hd ω lam Λ hΛ hω hf).comp hts)
  change Tendsto (fun n => (ts n : ℝ)⁻¹ * inner ℝ (f - S (ts n) f) v)
    atTop (𝓝 (E.form f v))
  simp_rw [he]
  exact hlim

/-- The physical evolution satisfies the integrated generator equation on compact
smooth tests, in the original weighted L² space. -/
theorem gmpPhysicalSemigroup_compactTest_integral {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) (t : ℝ≥0) :
    (gmpPhysicalSemigroup hd ω lam Λ hΛ hω) t
        (gmpPhysicalH1Value hd ω lam Λ hω
          (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hc)) -
      gmpPhysicalH1Value hd ω lam Λ hω
        (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hc) =
      ∫ s in (0 : ℝ)..(t : ℝ), (gmpPhysicalSemigroup hd ω lam Λ hΛ hω)
        (Real.toNNReal s)
        (EinsteinFull.C8GMP.compactTestGeneratorL2 hd ω hSmooth lam φ hφ hc) := by
  have h := (gmpPhysicalSemigroup hd ω lam Λ hΛ hω).operator_sub_eq_integral
    ⟨gmpPhysicalH1Value hd ω lam Λ hω
        (EinsteinFull.C8GMP.compactTestDomain hd lam φ hφ hc),
      gmpPhysicalSemigroup_compactTest_mem_generatorDomain hd ω lam Λ hΛ hω
        hSmooth φ hφ hc⟩ t
  rw [gmpPhysicalSemigroup_generator_compactTest] at h
  exact h

/-- The bounded Yosida generators agree on common C₀ and weighted L² inputs. -/
theorem gmpPhysicalYosidaGenerator_ae {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (α : PositiveShift)
    (f : ZeroAtInftyContinuousMap (Vec d) ℝ)
    (F : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hae : (F : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] f) :
    ((gmpPhysicalContractiveResolvent hd ω lam Λ hΛ hω).yosidaGenerator α F :
      Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam]
      (gmpPhysicalC0ContractiveResolvent hd ω lam Λ hΛ hω hSmooth).yosidaGenerator α f := by
  have hr := (gmpPhysicalC0Resolvent_ae_of_memLp hd ω lam Λ hΛ hω hSmooth
    α α.property f F hae).symm
  filter_upwards [hae, hr,
    Lp.coeFn_smul (α : ℝ) (gmpPhysicalResolvent hd ω lam Λ hΛ hω α α.property F),
    Lp.coeFn_sub ((α : ℝ) • gmpPhysicalResolvent hd ω lam Λ hΛ hω α α.property F) F,
    Lp.coeFn_smul (α : ℝ) (((α : ℝ) •
      gmpPhysicalResolvent hd ω lam Λ hΛ hω α α.property F) - F)] with x hf hr hs hdif ho
  change (((α : ℝ) • (((α : ℝ) •
    gmpPhysicalResolvent hd ω lam Λ hΛ hω α α.property F) - F) :
    Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) x) = _
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul] at ho hdif hs
  rw [ho, hdif, hs]
  change (α : ℝ) * ((α : ℝ) * _ - _) = (α : ℝ) * ((α : ℝ) * _ - _)
  rw [hr, hf]
  rfl

/-- All powers of the bounded Yosida generators agree on common inputs. -/
theorem gmpPhysicalYosidaGenerator_pow_ae {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (α : PositiveShift)
    (f : ZeroAtInftyContinuousMap (Vec d) ℝ)
    (F : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hae : (F : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] f) (n : ℕ) :
    (((gmpPhysicalContractiveResolvent hd ω lam Λ hΛ hω).yosidaGenerator α ^ n) F :
      Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam]
      ((gmpPhysicalC0ContractiveResolvent hd ω lam Λ hΛ hω hSmooth).yosidaGenerator α ^ n) f := by
  induction n with
  | zero => simpa using hae
  | succ n ih =>
      simpa only [pow_succ', ContinuousLinearMap.mul_apply] using
        gmpPhysicalYosidaGenerator_ae hd ω lam Λ hΛ hω hSmooth α _ _ ih

/-- Agreement of C₀ and weighted L² representatives passes to simultaneous limits. -/
theorem gmpPhysicalC0L2_ae_of_limits {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam : ℝ)
    (fn : ℕ → ZeroAtInftyContinuousMap (Vec d) ℝ)
    (Fn : ℕ → Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (f : ZeroAtInftyContinuousMap (Vec d) ℝ)
    (F : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hae : ∀ n, (Fn n : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] fn n)
    (hf : Tendsto fn atTop (𝓝 f)) (hF : Tendsto Fn atTop (𝓝 F)) :
    (F : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] f := by
  obtain ⟨ns, hns, hlim⟩ := (tendstoInMeasure_of_tendsto_Lp hF).exists_seq_tendsto_ae
  have hp (x : Vec d) : Tendsto (fun n => fn (ns n) x) atTop (𝓝 (f x)) := by
    have heval : Continuous (fun v : ZeroAtInftyContinuousMap (Vec d) ℝ => v x) :=
      (BoundedContinuousFunction.lipschitz_eval_const x).continuous.comp
        (ZeroAtInftyContinuousMap.isometry_toBCF.continuous)
    exact (heval.tendsto f).comp (hf.comp hns.tendsto_atTop)
  have he : ∀ᵐ x ∂physicalReversibleMeasure ω hd lam, ∀ n, Fn (ns n) x = fn (ns n) x := by
    exact ae_all_iff.mpr (fun n => hae (ns n))
  filter_upwards [hlim, he] with x hx heq
  apply tendsto_nhds_unique hx
  simpa only [heq] using hp x

/-- The bounded Yosida semigroups agree on common C₀ and weighted L² inputs. -/
theorem gmpPhysicalYosidaSemigroup_ae {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (α : PositiveShift) (t : ℝ≥0)
    (f : ZeroAtInftyContinuousMap (Vec d) ℝ)
    (F : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hae : (F : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] f) :
    ((gmpPhysicalContractiveResolvent hd ω lam Λ hΛ hω).yosidaSemigroup α t F :
      Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam]
      (gmpPhysicalC0ContractiveResolvent hd ω lam Λ hΛ hω hSmooth).yosidaSemigroup α t f := by
  let A := (t : ℝ) • (gmpPhysicalContractiveResolvent hd ω lam Λ hΛ hω).yosidaGenerator α
  let a := (t : ℝ) • (gmpPhysicalC0ContractiveResolvent hd ω lam Λ hΛ hω hSmooth).yosidaGenerator α
  have hp (n : ℕ) : ((A ^ n) F : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] (a ^ n) f := by
    induction n with
    | zero => simpa using hae
    | succ n ih =>
      have h := gmpPhysicalYosidaGenerator_ae hd ω lam Λ hΛ hω hSmooth α _ _ ih
      filter_upwards [h, Lp.coeFn_smul (t : ℝ)
        ((gmpPhysicalContractiveResolvent hd ω lam Λ hΛ hω).yosidaGenerator α ((A ^ n) F))] with x hx hs
      simp only [pow_succ', ContinuousLinearMap.mul_apply, A, a,
        ContinuousLinearMap.smul_apply] at hs ⊢
      simp only [Pi.smul_apply, smul_eq_mul] at hs
      rw [hs]
      change (t : ℝ) * _ = (t : ℝ) * _
      rw [hx]
      rfl
  let u (n : ℕ) := ((n.factorial : ℝ)⁻¹) • (A ^ n) F
  let v (n : ℕ) := ((n.factorial : ℝ)⁻¹) • (a ^ n) f
  have huv (n : ℕ) : (u n : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] v n := by
    filter_upwards [hp n, Lp.coeFn_smul ((n.factorial : ℝ)⁻¹) ((A ^ n) F)] with x hx hs
    change (((n.factorial : ℝ)⁻¹) • (A ^ n) F : Lp ℝ 2 _) x = _
    rw [hs]
    change ((n.factorial : ℝ)⁻¹) * _ = ((n.factorial : ℝ)⁻¹) * _
    rw [hx]
    rfl
  have hsum (n : ℕ) : ((∑ k ∈ Finset.range n, u k : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) : Vec d → ℝ) =ᵐ[
      physicalReversibleMeasure ω hd lam] ((∑ k ∈ Finset.range n, v k : ZeroAtInftyContinuousMap (Vec d) ℝ) : Vec d → ℝ) := by
    induction n with
    | zero => simpa using Lp.coeFn_zero ℝ 2 (physicalReversibleMeasure ω hd lam)
    | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      filter_upwards [ih, huv n, Lp.coeFn_add (∑ k ∈ Finset.range n, u k) (u n)] with x hx hy hz
      simp only [Pi.add_apply] at hz
      rw [hz]
      change (∑ k ∈ Finset.range n, u k : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) x + u n x =
        (∑ k ∈ Finset.range n, v k : ZeroAtInftyContinuousMap (Vec d) ℝ) x + v n x
      rw [hx, hy]
  have hL := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A).map
    (ContinuousLinearMap.apply ℝ _ F) (ContinuousLinearMap.continuous _)
  have hC := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) a).map
    (ContinuousLinearMap.apply ℝ _ f) (ContinuousLinearMap.continuous _)
  apply gmpPhysicalC0L2_ae_of_limits hd ω lam
    (fun n => ∑ k ∈ Finset.range n, v k) (fun n => ∑ k ∈ Finset.range n, u k) _ _ hsum
  · simpa [v, a, ContractiveResolvent.yosidaSemigroup_apply, ContractiveResolvent.yosidaOperator] using! hC.tendsto_sum_nat
  · simpa [u, A, ContractiveResolvent.yosidaSemigroup_apply, ContractiveResolvent.yosidaOperator] using! hL.tendsto_sum_nat

/-- The physical C₀ and weighted L² evolutions agree on common inputs. -/
theorem gmpPhysicalSemigroup_ae_of_memLp {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0)
    (f : ZeroAtInftyContinuousMap (Vec d) ℝ)
    (F : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hae : (F : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] f) :
    ((gmpPhysicalSemigroup hd ω lam Λ hΛ hω) t F : Vec d → ℝ) =ᵐ[
      physicalReversibleMeasure ω hd lam] (gmpPhysicalC0Semigroup hd ω lam Λ hΛ hω hSmooth) t f := by
  let R := gmpPhysicalContractiveResolvent hd ω lam Λ hΛ hω
  let r := gmpPhysicalC0ContractiveResolvent hd ω lam Λ hΛ hω hSmooth
  apply gmpPhysicalC0L2_ae_of_limits hd ω lam
    (fun n => r.yosidaSemigroup (naturalShift n) t f)
    (fun n => R.yosidaSemigroup (naturalShift n) t F) _ _
  · intro n
    exact gmpPhysicalYosidaSemigroup_ae hd ω lam Λ hΛ hω hSmooth (naturalShift n) t f F hae
  · exact r.tendsto_yosidaSemigroup_naturalShift_apply_generatedSemigroup t f
  · exact R.tendsto_yosidaSemigroup_naturalShift_apply_generatedSemigroup t F

/-- The physical spatial kernels represent the weighted L² evolution on common inputs. -/
theorem gmpPhysicalC0KernelSemigroup_integral_ae {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (t : ℝ≥0)
    (f : ZeroAtInftyContinuousMap (Vec d) ℝ)
    (F : Lp ℝ 2 (physicalReversibleMeasure ω hd lam))
    (hae : (F : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd lam] f) :
    ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
      ∫ y, f y ∂(gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x) =
        (gmpPhysicalSemigroup hd ω lam Λ hΛ hω) t F x := by
  filter_upwards [gmpPhysicalSemigroup_ae_of_memLp hd ω lam Λ hΛ hω hSmooth t f F hae] with x hx
  exact (gmpPhysicalC0KernelSemigroup_integral hd ω lam Λ hΛ hω hSmooth t f x).trans hx.symm

/-- A smooth compact observable moves by at most time times its generator norm. -/
theorem gmpPhysicalC0Semigroup_compactTest_norm_sub_le {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) (t : ℝ≥0) :
    ‖(gmpPhysicalC0Semigroup hd ω lam Λ hΛ hω hSmooth) t
        (gmpPhysicalCompactC0 φ hφ.continuous hc) - gmpPhysicalCompactC0 φ hφ.continuous hc‖ ≤
      ‖gmpPhysicalCompactC0 (physicalGenerator (firstCoordinateIndex hd) ω lam φ)
        (EinsteinFull.Work.W5.gantert_contDiff_physicalGenerator _ ω hSmooth lam hφ).continuous
        (EinsteinFull.Work.W5.gantert_hasCompactSupport_physicalGenerator _ ω lam hc)‖ * (t : ℝ) := by
  let S := gmpPhysicalC0Semigroup hd ω lam Λ hΛ hω hSmooth
  let u : S.generatorDomain := ⟨gmpPhysicalCompactC0 φ hφ.continuous hc,
    gmpPhysicalC0Semigroup_compactTest_mem_generatorDomain hd ω lam Λ hΛ hω hSmooth φ hφ hc⟩
  have h := S.operator_sub_eq_integral u t
  rw [← S.orbitIntegral_apply] at h
  have hg : S.generator u = gmpPhysicalCompactC0 (physicalGenerator (firstCoordinateIndex hd) ω lam φ)
      (EinsteinFull.Work.W5.gantert_contDiff_physicalGenerator _ ω hSmooth lam hφ).continuous
      (EinsteinFull.Work.W5.gantert_hasCompactSupport_physicalGenerator _ ω lam hc) :=
    gmpPhysicalC0Semigroup_generator_compactTest hd ω lam Λ hΛ hω hSmooth φ hφ hc
  rw [h, ← hg]
  exact S.norm_orbitIntegral_le (S.generator u) t

/-- The kernel increment of a smooth compact observable is controlled by its generator. -/
theorem gmpPhysicalC0KernelSemigroup_compactTest_sub_le {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) (t : ℝ≥0) (x : Vec d) :
    |(∫ y, φ y ∂(gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x)) - φ x| ≤
      ‖gmpPhysicalCompactC0 (physicalGenerator (firstCoordinateIndex hd) ω lam φ)
        (EinsteinFull.Work.W5.gantert_contDiff_physicalGenerator _ ω hSmooth lam hφ).continuous
        (EinsteinFull.Work.W5.gantert_hasCompactSupport_physicalGenerator _ ω lam hc)‖ * (t : ℝ) := by
  let u := gmpPhysicalCompactC0 φ hφ.continuous hc
  let v := (gmpPhysicalC0Semigroup hd ω lam Λ hΛ hω hSmooth) t u - u
  have hnorm : ‖v x‖ ≤ ‖v‖ := by
    simpa using BoundedContinuousFunction.norm_coe_le_norm v.toBCF x
  have hbound := gmpPhysicalC0Semigroup_compactTest_norm_sub_le hd ω lam Λ hΛ hω hSmooth φ hφ hc t
  have hi := gmpPhysicalC0KernelSemigroup_integral hd ω lam Λ hΛ hω hSmooth t u x
  change (∫ y, φ y ∂_) = _ at hi
  rw [hi]
  change ‖v x‖ ≤ _
  exact hnorm.trans hbound

/-- Smooth cutoffs with vanishing generator norm exclude loss of kernel mass. -/
theorem gmpPhysicalC0KernelSemigroup_conservative_of_cutoffs {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (χ : ℕ → Vec d → ℝ)
    (hs : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (χ n))
    (hc : ∀ n, HasCompactSupport (χ n))
    (hle : ∀ n x, χ n x ≤ 1)
    (hlim : ∀ x, Tendsto (fun n => χ n x) atTop (𝓝 1))
    (hgen : Tendsto (fun n => ‖gmpPhysicalCompactC0
      (physicalGenerator (firstCoordinateIndex hd) ω lam (χ n))
      (EinsteinFull.Work.W5.gantert_contDiff_physicalGenerator _ ω hSmooth lam (hs n)).continuous
      (EinsteinFull.Work.W5.gantert_hasCompactSupport_physicalGenerator _ ω lam (hc n))‖)
      atTop (𝓝 0)) :
    (gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth).IsConservative := by
  let P := gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth
  intro t x
  letI : ProbabilityTheory.IsFiniteKernel (P t) := (P.isSubMarkovKernel t).isFiniteKernel
  have hmass : P t x Set.univ ≤ 1 := P.measure_univ_le_one t x
  have hleMass (n : ℕ) : (∫ y, χ n y ∂(P t x)) ≤ (P t x).real Set.univ := by
    have hi : Integrable (χ n) (P t x) := (hs n).continuous.integrable_of_hasCompactSupport (hc n)
    have h := integral_mono hi (integrable_const (1 : ℝ)) (fun y => hle n y)
    simpa using h
  have hbound (n : ℕ) : χ n x ≤ (P t x).real Set.univ +
      ‖gmpPhysicalCompactC0 (physicalGenerator (firstCoordinateIndex hd) ω lam (χ n))
        (EinsteinFull.Work.W5.gantert_contDiff_physicalGenerator _ ω hSmooth lam (hs n)).continuous
        (EinsteinFull.Work.W5.gantert_hasCompactSupport_physicalGenerator _ ω lam (hc n))‖ * (t : ℝ) := by
    have h := gmpPhysicalC0KernelSemigroup_compactTest_sub_le hd ω lam Λ hΛ hω hSmooth
      (χ n) (hs n) (hc n) t x
    have h' := (abs_le.mp h).1
    linarith [hleMass n]
  have hlower : 1 ≤ (P t x).real Set.univ := by
    have ht := (show Tendsto (fun _ : ℕ => (P t x).real Set.univ) atTop
      (𝓝 ((P t x).real Set.univ)) from tendsto_const_nhds).add (hgen.mul_const (t : ℝ))
    have hh := le_of_tendsto_of_tendsto (hlim x) ht (Filter.Eventually.of_forall hbound)
    simpa using hh
  have hr : (1 : ℝ) ≤ (P t x Set.univ).toReal := hlower
  apply le_antisymm hmass
  exact (ENNReal.toReal_le_toReal (by simp) (ne_of_lt (lt_of_le_of_lt hmass (by simp)))).mp (by simpa using hr)

/-- A smooth compact observable has uniformly bounded first and second
coordinate derivatives, with a single constant for all coordinates. -/
theorem gmpPhysical_compactTest_derivative_bounds {d : ℕ} (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    ∃ B : ℝ, 0 ≤ B ∧
      (∀ x i, |fderiv ℝ φ x (unitVector i)| ≤ B) ∧
      ∀ x i j, |fderiv ℝ (fun y => fderiv ℝ φ y (unitVector j)) x (unitVector i)| ≤ B := by
  have hs (j : Fin d) : ContDiff ℝ (⊤ : ℕ∞)
      (fun y => fderiv ℝ φ y (unitVector j)) :=
    (contDiff_infty_iff_fderiv.mp hφ).2.clm_apply contDiff_const
  have hc' (j : Fin d) : HasCompactSupport (fun y => fderiv ℝ φ y (unitVector j)) :=
    hc.fderiv_apply ℝ (unitVector j)
  have hfirst (i : Fin d) : ∃ b : ℝ, ∀ x, ‖fderiv ℝ φ x (unitVector i)‖ ≤ b :=
    (((contDiff_infty_iff_fderiv.mp hφ).2.clm_apply contDiff_const).continuous).bounded_above_of_compact_support (hc' i)
  have hsecond (i j : Fin d) : ∃ b : ℝ, ∀ x,
      ‖fderiv ℝ (fun y => fderiv ℝ φ y (unitVector j)) x (unitVector i)‖ ≤ b :=
    (((contDiff_infty_iff_fderiv.mp (hs j)).2.clm_apply contDiff_const).continuous).bounded_above_of_compact_support
      ((hc' j).fderiv_apply ℝ (unitVector i))
  choose b hb using hfirst
  choose c hcBound using hsecond
  have hb0 (i : Fin d) : 0 ≤ b i := (norm_nonneg _).trans (hb i 0)
  have hc0 (i j : Fin d) : 0 ≤ c i j := (norm_nonneg _).trans (hcBound i j 0)
  refine ⟨(∑ i, b i) + ∑ i, ∑ j, c i j, ?_, ?_, ?_⟩
  · exact add_nonneg (Finset.sum_nonneg fun i _ => hb0 i)
      (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hc0 i j)
  · intro x i
    have h := hb i x
    rw [Real.norm_eq_abs] at h
    have hbSum : b i ≤ ∑ i, b i := Finset.single_le_sum (fun j _ => hb0 j) (Finset.mem_univ i)
    have hcSum : 0 ≤ ∑ i, ∑ j, c i j := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hc0 i j
    linarith
  · intro x i j
    have h := hcBound i j x
    rw [Real.norm_eq_abs] at h
    have hInner : c i j ≤ ∑ k, c i k := Finset.single_le_sum (fun k _ => hc0 i k) (Finset.mem_univ j)
    have hOuter : (∑ k, c i k) ≤ ∑ k, ∑ l, c k l :=
      Finset.single_le_sum (fun k _ => Finset.sum_nonneg fun l _ => hc0 k l) (Finset.mem_univ i)
    have hbSum : 0 ≤ ∑ i, b i := Finset.sum_nonneg fun i _ => hb0 i
    linarith

/-- Coordinate derivatives of a dilated test scale by one power per derivative. -/
theorem gmpPhysical_scaledTest_derivatives {d : ℕ} (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (a : ℝ) (x : Vec d) (i j : Fin d) :
    fderiv ℝ (fun y => φ (a • y)) x (unitVector i) =
      a * fderiv ℝ φ (a • x) (unitVector i) ∧
    fderiv ℝ (fun y => fderiv ℝ (fun z => φ (a • z)) y (unitVector j)) x (unitVector i) =
      a ^ 2 * fderiv ℝ (fun y => fderiv ℝ φ y (unitVector j)) (a • x) (unitVector i) := by
  have hscale (f : Vec d → ℝ) (hf : Differentiable ℝ f) (y : Vec d) (k : Fin d) :
      fderiv ℝ (fun z => f (a • z)) y (unitVector k) =
        a * fderiv ℝ f (a • y) (unitVector k) := by
    have hd := ((hf (a • y)).hasFDerivAt.comp y ((hasFDerivAt_id y).const_smul a)).fderiv
    change fderiv ℝ (fun z => f (a • z)) y = _ at hd
    simpa using congrArg (fun L : Vec d →L[ℝ] ℝ => L (unitVector k)) hd
  have hd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hg : Differentiable ℝ (fun y => fderiv ℝ φ y (unitVector j)) :=
    ((contDiff_infty_iff_fderiv.mp hφ).2.clm_apply contDiff_const).differentiable (by simp)
  refine ⟨hscale φ hd x i, ?_⟩
  have heq : (fun y => fderiv ℝ (fun z => φ (a • z)) y (unitVector j)) =
      (fun y => a * fderiv ℝ φ (a • y) (unitVector j)) := by
    funext y
    exact hscale φ hd y j
  rw [heq, fderiv_const_mul]
  · rw [smul_apply, smul_eq_mul, hscale _ hg x i]
    ring
  · exact (hg (a • x)).comp x (differentiableAt_id.const_smul a)

/-- Uniform coordinate-derivative bounds control the physical generator. -/
theorem gmpPhysical_generator_bound_of_derivatives {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : Vec d → ℝ), ContDiff ℝ 2 φ →
      ∀ D : ℝ, 0 ≤ D →
      (∀ x i, |fderiv ℝ φ x (unitVector i)| ≤ D) →
      (∀ x i j, |fderiv ℝ (fun y => fderiv ℝ φ y (unitVector j)) x (unitVector i)| ≤ D) →
      ∀ x, |physicalGenerator (firstCoordinateIndex hd) ω lam φ x| ≤ C * D := by
  obtain ⟨_, _, ⟨A, hA⟩, _, _, ⟨B, hB⟩⟩ :=
    EinsteinFull.physical_svHypotheses (by linarith : 0 < Λ) hω (firstCoordinateIndex hd) lam
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0 (firstCoordinateIndex hd) (firstCoordinateIndex hd))
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 (firstCoordinateIndex hd))
  refine ⟨((d : ℝ) * d * A / 2 + d * B), by positivity, ?_⟩
  intro φ hφ D hD hfirst hsecond x
  rw [EinsteinFull.physicalGenerator_eq_svGenerator hSmooth _ lam hφ x]
  unfold EinsteinFull.External.Draft.svGenerator
  have hsecondSum : |∑ i : Fin d, ∑ j : Fin d, ω.1 x i j *
      fderiv ℝ (fun y => fderiv ℝ φ y (unitVector j)) x (unitVector i)| ≤
      (d : ℝ) * d * (A * D) := by
    calc
      _ ≤ ∑ i : Fin d, ∑ j : Fin d, |ω.1 x i j *
          fderiv ℝ (fun y => fderiv ℝ φ y (unitVector j)) x (unitVector i)| := by
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, A * D := by
        apply Finset.sum_le_sum; intro i _; apply Finset.sum_le_sum; intro j _
        rw [abs_mul]
        exact mul_le_mul (hA x i j) (hsecond x i j) (abs_nonneg _) hA0
      _ = _ := by simp; ring
  have hfirstSum : |∑ i : Fin d, EinsteinFull.physicalDrift ω (firstCoordinateIndex hd) lam x i *
      fderiv ℝ φ x (unitVector i)| ≤ (d : ℝ) * (B * D) := by
    calc
      _ ≤ ∑ i : Fin d, |EinsteinFull.physicalDrift ω (firstCoordinateIndex hd) lam x i *
          fderiv ℝ φ x (unitVector i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin d, B * D := by
        apply Finset.sum_le_sum; intro i _; rw [abs_mul]
        exact mul_le_mul (hB x i) (hfirst x i) (abs_nonneg _) hB0
      _ = _ := by simp
  calc
    _ ≤ |(1 / 2 : ℝ) * (∑ i : Fin d, ∑ j : Fin d, ω.1 x i j *
      fderiv ℝ (fun y => fderiv ℝ φ y (unitVector j)) x (unitVector i))| +
      |∑ i : Fin d, EinsteinFull.physicalDrift ω (firstCoordinateIndex hd) lam x i *
      fderiv ℝ φ x (unitVector i)| := abs_add_le _ _
    _ ≤ (1 / 2 : ℝ) * ((d : ℝ) * d * (A * D)) + d * (B * D) := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      exact add_le_add (mul_le_mul_of_nonneg_left hsecondSum (by norm_num)) hfirstSum
    _ = _ := by ring

/-- Pointwise first and second derivative bounds separately control the physical generator. -/
theorem gmpPhysical_generator_bound_of_pointwise_derivatives {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ (φ : Vec d → ℝ), ContDiff ℝ 2 φ →
      ∀ (x : Vec d) (D₁ D₂ : ℝ), 0 ≤ D₁ → 0 ≤ D₂ →
      (∀ i, |fderiv ℝ φ x (unitVector i)| ≤ D₁) →
      (∀ i j, |fderiv ℝ (fun y => fderiv ℝ φ y (unitVector j)) x (unitVector i)| ≤ D₂) →
      |physicalGenerator (firstCoordinateIndex hd) ω lam φ x| ≤ C₁ * D₁ + C₂ * D₂ := by
  obtain ⟨_, _, ⟨A, hA⟩, _, _, ⟨B, hB⟩⟩ :=
    EinsteinFull.physical_svHypotheses (by linarith : 0 < Λ) hω (firstCoordinateIndex hd) lam
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0 (firstCoordinateIndex hd) (firstCoordinateIndex hd))
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 (firstCoordinateIndex hd))
  refine ⟨d * B, (d : ℝ) * d * A / 2, by positivity, by positivity, ?_⟩
  intro φ hφ x D₁ D₂ hD₁ hD₂ hfirst hsecond
  rw [EinsteinFull.physicalGenerator_eq_svGenerator hSmooth _ lam hφ x]
  unfold EinsteinFull.External.Draft.svGenerator
  have hsecondSum : |∑ i : Fin d, ∑ j : Fin d, ω.1 x i j *
      fderiv ℝ (fun y => fderiv ℝ φ y (unitVector j)) x (unitVector i)| ≤
      (d : ℝ) * d * (A * D₂) := by
    calc
      _ ≤ ∑ i : Fin d, ∑ j : Fin d, |ω.1 x i j *
          fderiv ℝ (fun y => fderiv ℝ φ y (unitVector j)) x (unitVector i)| := by
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, A * D₂ := by
        apply Finset.sum_le_sum; intro i _; apply Finset.sum_le_sum; intro j _
        rw [abs_mul]
        exact mul_le_mul (hA x i j) (hsecond i j) (abs_nonneg _) hA0
      _ = _ := by simp; ring
  have hfirstSum : |∑ i : Fin d, EinsteinFull.physicalDrift ω (firstCoordinateIndex hd) lam x i *
      fderiv ℝ φ x (unitVector i)| ≤ (d : ℝ) * (B * D₁) := by
    calc
      _ ≤ ∑ i : Fin d, |EinsteinFull.physicalDrift ω (firstCoordinateIndex hd) lam x i *
          fderiv ℝ φ x (unitVector i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin d, B * D₁ := by
        apply Finset.sum_le_sum; intro i _; rw [abs_mul]
        exact mul_le_mul (hB x i) (hfirst i) (abs_nonneg _) hB0
      _ = _ := by simp
  calc
    _ ≤ |(1 / 2 : ℝ) * (∑ i : Fin d, ∑ j : Fin d, ω.1 x i j *
      fderiv ℝ (fun y => fderiv ℝ φ y (unitVector j)) x (unitVector i))| +
      |∑ i : Fin d, EinsteinFull.physicalDrift ω (firstCoordinateIndex hd) lam x i *
      fderiv ℝ φ x (unitVector i)| := abs_add_le _ _
    _ ≤ (1 / 2 : ℝ) * ((d : ℝ) * d * (A * D₂)) + d * (B * D₁) := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      exact add_le_add (mul_le_mul_of_nonneg_left hsecondSum (by norm_num)) hfirstSum
    _ = _ := by ring

/-- The generator of a dilated compact test vanishes uniformly with the scale. -/
theorem gmpPhysical_scaledTest_generator_bound {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 ≤ a → a ≤ 1 → ∀ x,
      |physicalGenerator (firstCoordinateIndex hd) ω lam (fun y => φ (a • y)) x| ≤ C * a := by
  obtain ⟨B, hB, hfirst, hsecond⟩ := gmpPhysical_compactTest_derivative_bounds φ hφ hc
  obtain ⟨C, hC, hgen⟩ := gmpPhysical_generator_bound_of_derivatives hd ω lam Λ hΛ hω hSmooth
  refine ⟨C * B, mul_nonneg hC hB, ?_⟩
  intro a ha ha1 x
  have hs : ContDiff ℝ 2 (fun y : Vec d => φ (a • y)) :=
    (hφ.comp (contDiff_const_smul a)).of_le (by simp)
  have hf (y : Vec d) (i : Fin d) :
      |fderiv ℝ (fun z => φ (a • z)) y (unitVector i)| ≤ B * a := by
    rw [(gmpPhysical_scaledTest_derivatives φ hφ a y i i).1, abs_mul, abs_of_nonneg ha]
    nlinarith [hfirst (a • y) i]
  have hh (y : Vec d) (i j : Fin d) :
      |fderiv ℝ (fun z => fderiv ℝ (fun w => φ (a • w)) z (unitVector j)) y (unitVector i)| ≤ B * a := by
    rw [(gmpPhysical_scaledTest_derivatives φ hφ a y i j).2, abs_mul,
      abs_of_nonneg (sq_nonneg a)]
    have hsq : a ^ 2 ≤ a := by nlinarith
    have h := hsecond (a • y) i j
    calc
      a ^ 2 * |fderiv ℝ (fun z => fderiv ℝ φ z (unitVector j)) (a • y) (unitVector i)| ≤ a ^ 2 * B :=
        mul_le_mul_of_nonneg_left h (sq_nonneg a)
      _ ≤ a * B := mul_le_mul_of_nonneg_right hsq hB
      _ = B * a := by ring
  have h := hgen _ hs (B * a) (mul_nonneg hB ha) hf hh x
  convert h using 1 <;> ring

/-- Smooth regular physical environments generate conservative spatial kernels. -/
theorem gmpPhysicalC0KernelSemigroup_conservative {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) :
    (gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth).IsConservative := by
  let b : ContDiffBump (0 : Vec d) := ⟨1, 2, one_pos, one_lt_two⟩
  let a : ℕ → ℝ := fun n => ((n : ℝ) + 1)⁻¹
  let χ : ℕ → Vec d → ℝ := fun n x => b (a n • x)
  have ha (n : ℕ) : 0 < a n := by dsimp [a]; positivity
  have ha1 (n : ℕ) : a n ≤ 1 := by
    dsimp [a]
    exact (inv_le_one₀ (by positivity)).2 (by nlinarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n])
  have hat : Tendsto a atTop (𝓝 0) := by
    simpa only [a, one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hs (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (χ n) := b.contDiff.comp (contDiff_const_smul (a n))
  have hc (n : ℕ) : HasCompactSupport (χ n) := b.hasCompactSupport.comp_smul (ha n).ne'
  have hb0 : b 0 = 1 := b.one_of_mem_closedBall (by simp [b])
  have hlim (x : Vec d) : Tendsto (fun n => χ n x) atTop (𝓝 1) := by
    have ht : Tendsto (fun n => a n • x) atTop (𝓝 (0 : Vec d)) := by
      simpa only [zero_smul] using hat.smul (tendsto_const_nhds (x := x))
    simpa only [χ, hb0, Function.comp_def] using (b.continuous.tendsto 0).comp ht
  obtain ⟨C, hC, hbound⟩ := gmpPhysical_scaledTest_generator_bound hd ω lam Λ hΛ hω hSmooth b b.contDiff b.hasCompactSupport
  have hnorm (n : ℕ) : ‖gmpPhysicalCompactC0
      (physicalGenerator (firstCoordinateIndex hd) ω lam (χ n))
      (EinsteinFull.Work.W5.gantert_contDiff_physicalGenerator _ ω hSmooth lam (hs n)).continuous
      (EinsteinFull.Work.W5.gantert_hasCompactSupport_physicalGenerator _ ω lam (hc n))‖ ≤ C * a n := by
    change ‖(gmpPhysicalCompactC0
      (physicalGenerator (firstCoordinateIndex hd) ω lam (χ n))
      (EinsteinFull.Work.W5.gantert_contDiff_physicalGenerator _ ω hSmooth lam (hs n)).continuous
      (EinsteinFull.Work.W5.gantert_hasCompactSupport_physicalGenerator _ ω lam (hc n))).toBCF‖ ≤ C * a n
    apply (BoundedContinuousFunction.norm_le (mul_nonneg hC (ha n).le)).2
    intro x
    change |physicalGenerator (firstCoordinateIndex hd) ω lam (χ n) x| ≤ C * a n
    exact hbound (a n) (ha n).le (ha1 n) x
  apply gmpPhysicalC0KernelSemigroup_conservative_of_cutoffs hd ω lam Λ hΛ hω hSmooth χ hs hc
    (fun n x => b.le_one) hlim
  have hzero : Tendsto (fun n => C * a n) atTop (𝓝 0) := by simpa using hat.const_mul C
  exact squeeze_zero (fun n => norm_nonneg _) hnorm hzero

/-- Translation preserves the first two coordinate derivatives of a test. -/
theorem gmpPhysical_translatedTest_derivatives {d : ℕ} (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (z x : Vec d) (i j : Fin d) :
    fderiv ℝ (fun y => φ (y - z)) x (unitVector i) =
      fderiv ℝ φ (x - z) (unitVector i) ∧
    fderiv ℝ (fun y => fderiv ℝ (fun w => φ (w - z)) y (unitVector j)) x (unitVector i) =
      fderiv ℝ (fun y => fderiv ℝ φ y (unitVector j)) (x - z) (unitVector i) := by
  have htrans (f : Vec d → ℝ) (hf : Differentiable ℝ f) (y : Vec d) (k : Fin d) :
      fderiv ℝ (fun w => f (w - z)) y (unitVector k) =
        fderiv ℝ f (y - z) (unitVector k) := by
    have h := ((hf (y - z)).hasFDerivAt.comp y (hasFDerivAt_sub_const z)).fderiv
    change fderiv ℝ (fun w => f (w - z)) y = _ at h
    simpa using congrArg (fun L : Vec d →L[ℝ] ℝ => L (unitVector k)) h
  have hd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hg : Differentiable ℝ (fun y => fderiv ℝ φ y (unitVector j)) :=
    ((contDiff_infty_iff_fderiv.mp hφ).2.clm_apply contDiff_const).differentiable (by simp)
  refine ⟨htrans φ hd x i, ?_⟩
  have heq : (fun y => fderiv ℝ (fun w => φ (w - z)) y (unitVector j)) =
      (fun y => fderiv ℝ φ (y - z) (unitVector j)) := by
    funext y
    exact htrans φ hd y j
  rw [heq]
  exact htrans _ hg x i

/-- The scaled-test generator estimate is uniform over all translation centers. -/
theorem gmpPhysical_shiftedScaledTest_generator_bound {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 ≤ a → a ≤ 1 → ∀ z x,
      |physicalGenerator (firstCoordinateIndex hd) ω lam (fun y => φ (a • (y - z))) x| ≤ C * a := by
  obtain ⟨B, hB, hfirst, hsecond⟩ := gmpPhysical_compactTest_derivative_bounds φ hφ hc
  obtain ⟨C, hC, hgen⟩ := gmpPhysical_generator_bound_of_derivatives hd ω lam Λ hΛ hω hSmooth
  refine ⟨C * B, mul_nonneg hC hB, ?_⟩
  intro a ha ha1 z x
  let ψ : Vec d → ℝ := fun y => φ (a • y)
  have hs : ContDiff ℝ (⊤ : ℕ∞) ψ := hφ.comp (contDiff_const_smul a)
  have ht : ContDiff ℝ 2 (fun y : Vec d => ψ (y - z)) :=
    (hs.comp (contDiff_id.sub contDiff_const)).of_le (by simp)
  have hf (y : Vec d) (i : Fin d) :
      |fderiv ℝ (fun w => ψ (w - z)) y (unitVector i)| ≤ B * a := by
    rw [(gmpPhysical_translatedTest_derivatives ψ hs z y i i).1,
      (gmpPhysical_scaledTest_derivatives φ hφ a (y - z) i i).1,
      abs_mul, abs_of_nonneg ha]
    nlinarith [hfirst (a • (y - z)) i]
  have hh (y : Vec d) (i j : Fin d) :
      |fderiv ℝ (fun w => fderiv ℝ (fun v => ψ (v - z)) w (unitVector j)) y (unitVector i)| ≤ B * a := by
    rw [(gmpPhysical_translatedTest_derivatives ψ hs z y i j).2,
      (gmpPhysical_scaledTest_derivatives φ hφ a (y - z) i j).2,
      abs_mul, abs_of_nonneg (sq_nonneg a)]
    have hsq : a ^ 2 ≤ a := by nlinarith
    have h := hsecond (a • (y - z)) i j
    calc
      a ^ 2 * |fderiv ℝ (fun w => fderiv ℝ φ w (unitVector j)) (a • (y - z)) (unitVector i)| ≤ a ^ 2 * B :=
        mul_le_mul_of_nonneg_left h (sq_nonneg a)
      _ ≤ a * B := mul_le_mul_of_nonneg_right hsq hB
      _ = B * a := by ring
  have h := hgen _ ht (B * a) (mul_nonneg hB ha) hf hh x
  convert h using 1 <;> ring

/-- Translated dilations have a kernel increment bound uniform in their center. -/
theorem gmpPhysicalC0KernelSemigroup_shiftedScaledTest_sub_le {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 < a → a ≤ 1 → ∀ (z x : Vec d) (t : ℝ≥0),
      |(∫ y, φ (a • (y - z)) ∂(gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x)) -
        φ (a • (x - z))| ≤ C * a * (t : ℝ) := by
  obtain ⟨C, hC, hgen⟩ := gmpPhysical_shiftedScaledTest_generator_bound hd ω lam Λ hΛ hω hSmooth φ hφ hc
  refine ⟨C, hC, ?_⟩
  intro a ha ha1 z x t
  let ψ : Vec d → ℝ := fun y => φ (a • (y - z))
  have hs : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    hφ.comp ((contDiff_id.sub contDiff_const).const_smul a)
  have hcs : HasCompactSupport ψ := by
    simpa [ψ, sub_eq_add_neg, Function.comp_def] using
      ((hc.comp_smul ha.ne').comp_homeomorph (Homeomorph.addRight (-z)))
  have hn : ‖gmpPhysicalCompactC0 (physicalGenerator (firstCoordinateIndex hd) ω lam ψ)
      (EinsteinFull.Work.W5.gantert_contDiff_physicalGenerator _ ω hSmooth lam hs).continuous
      (EinsteinFull.Work.W5.gantert_hasCompactSupport_physicalGenerator _ ω lam hcs)‖ ≤ C * a := by
    change ‖(gmpPhysicalCompactC0 (physicalGenerator (firstCoordinateIndex hd) ω lam ψ)
      (EinsteinFull.Work.W5.gantert_contDiff_physicalGenerator _ ω hSmooth lam hs).continuous
      (EinsteinFull.Work.W5.gantert_hasCompactSupport_physicalGenerator _ ω lam hcs)).toBCF‖ ≤ C * a
    apply (BoundedContinuousFunction.norm_le (mul_nonneg hC ha.le)).2
    intro y
    exact hgen a ha.le ha1 z y
  have h := gmpPhysicalC0KernelSemigroup_compactTest_sub_le hd ω lam Λ hΛ hω hSmooth ψ hs hcs t x
  exact h.trans (mul_le_mul_of_nonneg_right hn (NNReal.coe_nonneg t))

/-- A uniform displacement tail bound from translated compact cutoffs. -/
theorem gmpPhysicalC0KernelSemigroup_displacement_tail {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 < a → a ≤ 1 → ∀ (x : Vec d) (t : ℝ≥0),
      (gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x)
        {y | 2 ≤ ‖a • (y - x)‖} ≤ ENNReal.ofReal (C * a * (t : ℝ)) := by
  let b : ContDiffBump (0 : Vec d) := ⟨1, 2, one_pos, one_lt_two⟩
  obtain ⟨C, hC, hbound⟩ :=
    gmpPhysicalC0KernelSemigroup_shiftedScaledTest_sub_le hd ω lam Λ hΛ hω hSmooth
      b b.contDiff b.hasCompactSupport
  refine ⟨C, hC, ?_⟩
  intro a ha ha1 x t
  let P := gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth
  let μ := P t x
  letI : ProbabilityTheory.IsFiniteKernel (P t) := (P.isSubMarkovKernel t).isFiniteKernel
  letI : IsProbabilityMeasure μ := ⟨gmpPhysicalC0KernelSemigroup_conservative hd ω lam Λ hΛ hω hSmooth t x⟩
  let f : Vec d → ℝ := fun y => b (a • (y - x))
  have hf : Integrable f μ := by
    have hs : ContDiff ℝ (⊤ : ℕ∞) f := b.contDiff.comp ((contDiff_id.sub contDiff_const).const_smul a)
    have hc : HasCompactSupport f := by
      simpa [f, sub_eq_add_neg, Function.comp_def] using
        ((b.hasCompactSupport.comp_smul ha.ne').comp_homeomorph (Homeomorph.addRight (-x)))
    exact hs.continuous.integrable_of_hasCompactSupport hc
  have hf0 : f x = 1 := by
    simpa [f] using b.one_of_mem_closedBall (by simp [b])
  have hi : ∫ y, (1 - f y) ∂μ ≤ C * a * (t : ℝ) := by
    have h := hbound a ha ha1 x x t
    change |(∫ y, f y ∂μ) - f x| ≤ _ at h
    rw [hf0] at h
    rw [integral_sub (integrable_const (1 : ℝ)) hf]
    simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
    linarith [(abs_le.mp h).1]
  have hm := (integrable_const (1 : ℝ)).sub hf
  calc
    μ {y | 2 ≤ ‖a • (y - x)‖} ≤ ENNReal.ofReal (∫ y, (1 - f y) ∂μ) := by
      apply hm.measure_le_integral (Filter.Eventually.of_forall (fun y => sub_nonneg.mpr b.le_one))
      intro y hy
      have hb : b (a • (y - x)) = 0 := by
        apply b.zero_of_le_dist
        simpa [b, dist_zero_right] using hy
      simp [f, hb]
    _ ≤ ENNReal.ofReal (C * a * (t : ℝ)) := ENNReal.ofReal_le_ofReal hi

/-- Coordinate squares have the drift-plus-diffusion growth needed for moment estimates. -/
theorem gmpPhysical_generator_coordinate_square_bound {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ (z x : Vec d) (k : Fin d),
      |physicalGenerator (firstCoordinateIndex hd) ω lam
        (fun y => (y k - z k) ^ 2) x| ≤ A * |x k - z k| + B := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hg⟩ :=
    gmpPhysical_generator_bound_of_pointwise_derivatives hd ω lam Λ hΛ hω hSmooth
  refine ⟨2 * C₁, 2 * C₂, by positivity, by positivity, ?_⟩
  intro z x k
  let f : Vec d → ℝ := fun y => y k - z k
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := (contDiff_apply ℝ ℝ k).sub contDiff_const
  have hdf (y : Vec d) : fderiv ℝ f y = ContinuousLinearMap.proj k := by
    exact ((hasFDerivAt_apply (𝕜 := ℝ) k y).sub_const (z k)).fderiv
  have hfirst (y : Vec d) (i : Fin d) :
      fderiv ℝ (fun w => f w ^ 2) y (unitVector i) =
        2 * f y * (if k = i then 1 else 0) := by
    rw [fderiv_fun_pow 2 (hf.differentiable (by simp) y), hdf]
    simp [unitVector, Pi.single_apply, eq_comm, mul_comm, mul_left_comm]
  have hsecond (y : Vec d) (i j : Fin d) :
      fderiv ℝ (fun w => fderiv ℝ (fun v => f v ^ 2) w (unitVector j)) y (unitVector i) =
        2 * (if k = j then 1 else 0) * (if k = i then 1 else 0) := by
    have he : (fun w => fderiv ℝ (fun v => f v ^ 2) w (unitVector j)) =
        fun w => (2 * (if k = j then 1 else 0)) * f w := by
      funext w
      rw [hfirst]
      ring
    rw [he, fderiv_const_mul]
    · rw [hdf]
      split_ifs <;> simp_all [unitVector, Pi.single_apply]
    · exact hf.differentiable (by simp) y
  have h1 (i : Fin d) : |fderiv ℝ (fun y => f y ^ 2) x (unitVector i)| ≤ 2 * |f x| := by
    rw [hfirst]
    split_ifs <;> simp [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
  have h2 (i j : Fin d) :
      |fderiv ℝ (fun y => fderiv ℝ (fun v => f v ^ 2) y (unitVector j)) x (unitVector i)| ≤ 2 := by
    rw [hsecond]
    split_ifs <;> norm_num
  have h := hg (fun y => f y ^ 2) ((hf.pow 2).of_le (by simp)) x
    (2 * |f x|) 2 (by positivity) (by norm_num) h1 h2
  change |physicalGenerator _ ω lam (fun y => (y k - z k) ^ 2) x| ≤ _ at h
  convert h using 1 <;> dsimp [f] <;> ring

/-- The generator of a fourth coordinate power has cubic drift and quadratic diffusion growth. -/
theorem gmpPhysical_generator_coordinate_fourth_bound {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ (z x : Vec d) (k : Fin d),
      |physicalGenerator (firstCoordinateIndex hd) ω lam
        (fun y => (y k - z k) ^ 4) x| ≤
          A * |x k - z k| ^ 3 + B * |x k - z k| ^ 2 := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hg⟩ :=
    gmpPhysical_generator_bound_of_pointwise_derivatives hd ω lam Λ hΛ hω hSmooth
  refine ⟨4 * C₁, 12 * C₂, by positivity, by positivity, ?_⟩
  intro z x k
  let f : Vec d → ℝ := fun y => y k - z k
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := (contDiff_apply ℝ ℝ k).sub contDiff_const
  have hdf (y : Vec d) : fderiv ℝ f y = ContinuousLinearMap.proj k := by
    exact ((hasFDerivAt_apply (𝕜 := ℝ) k y).sub_const (z k)).fderiv
  have hfirst (y : Vec d) (i : Fin d) :
      fderiv ℝ (fun w => f w ^ 4) y (unitVector i) =
        4 * f y ^ 3 * (if k = i then 1 else 0) := by
    rw [fderiv_fun_pow 4 (hf.differentiable (by simp) y), hdf]
    simp [unitVector, Pi.single_apply, mul_comm, mul_left_comm]
  have hsecond (y : Vec d) (i j : Fin d) :
      fderiv ℝ (fun w => fderiv ℝ (fun v => f v ^ 4) w (unitVector j)) y (unitVector i) =
        12 * f y ^ 2 * (if k = j then 1 else 0) * (if k = i then 1 else 0) := by
    have he : (fun w => fderiv ℝ (fun v => f v ^ 4) w (unitVector j)) =
        fun w => (4 * (if k = j then 1 else 0)) * f w ^ 3 := by
      funext w
      rw [hfirst]
      ring
    rw [he, fderiv_const_mul]
    · rw [fderiv_fun_pow 3 (hf.differentiable (by simp) y), hdf]
      split_ifs <;> simp_all [unitVector, Pi.single_apply, mul_comm, mul_left_comm] <;> ring
    · exact (hf.pow 3).differentiable (by simp) y
  have h1 (i : Fin d) : |fderiv ℝ (fun y => f y ^ 4) x (unitVector i)| ≤ 4 * |f x| ^ 3 := by
    rw [hfirst]
    split_ifs <;> simp [abs_mul, abs_pow]
  have h2 (i j : Fin d) :
      |fderiv ℝ (fun y => fderiv ℝ (fun v => f v ^ 4) y (unitVector j)) x (unitVector i)| ≤
        12 * |f x| ^ 2 := by
    rw [hsecond]
    split_ifs <;> simp [abs_mul, abs_pow, sq_nonneg]
  have h := hg (fun y => f y ^ 4) ((hf.pow 4).of_le (by simp)) x
    (4 * |f x| ^ 3) (12 * |f x| ^ 2) (by positivity) (by positivity) h1 h2
  change |physicalGenerator _ ω lam (fun y => (y k - z k) ^ 4) x| ≤ _ at h
  convert h using 1 <;> dsimp [f] <;> ring

/-- Dynkin's integral identity for compact smooth tests of the actual physical kernels. -/
theorem gmpPhysicalC0KernelSemigroup_compactTest_dynkin {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) (φ : Vec d → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (t : ℝ≥0) (x : Vec d) :
    (∫ y, φ y ∂(gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x)) - φ x =
      ∫ s in (0 : ℝ)..(t : ℝ), ∫ y,
        physicalGenerator (firstCoordinateIndex hd) ω lam φ y
          ∂(gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth (Real.toNNReal s) x) := by
  let S := gmpPhysicalC0Semigroup hd ω lam Λ hΛ hω hSmooth
  let u : S.generatorDomain := ⟨gmpPhysicalCompactC0 φ hφ.continuous hc,
    gmpPhysicalC0Semigroup_compactTest_mem_generatorDomain hd ω lam Λ hΛ hω hSmooth φ hφ hc⟩
  let g := gmpPhysicalCompactC0 (physicalGenerator (firstCoordinateIndex hd) ω lam φ)
      (EinsteinFull.Work.W5.gantert_contDiff_physicalGenerator _ ω hSmooth lam hφ).continuous
      (EinsteinFull.Work.W5.gantert_hasCompactSupport_physicalGenerator _ ω lam hc)
  have hg : S.generator u = g :=
    gmpPhysicalC0Semigroup_generator_compactTest hd ω lam Λ hΛ hω hSmooth φ hφ hc
  let ev : ZeroAtInftyContinuousMap (Vec d) ℝ →L[ℝ] ℝ :=
    LinearMap.mkContinuous
      { toFun := fun f => f x
        map_add' := by intro f g; rfl
        map_smul' := by intro c f; rfl } 1 (by
          intro f
          simpa using BoundedContinuousFunction.norm_coe_le_norm f.toBCF x)
  have h := congrArg ev (S.operator_sub_eq_integral u t)
  rw [hg, ← ev.intervalIntegral_comp_comm ((S.continuous_operator_toNNReal g).intervalIntegrable 0 t)] at h
  have hi := gmpPhysicalC0KernelSemigroup_integral hd ω lam Λ hΛ hω hSmooth t
    (gmpPhysicalCompactC0 φ hφ.continuous hc) x
  change (∫ y, φ y ∂_) = _ at hi
  rw [hi]
  change S t u x - (u : ZeroAtInftyContinuousMap (Vec d) ℝ) x = _
  calc
    _ = ∫ s in (0 : ℝ)..(t : ℝ), S (Real.toNNReal s) g x := by simpa [ev] using h
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro s hs
      symm
      exact gmpPhysicalC0KernelSemigroup_integral hd ω lam Λ hΛ hω hSmooth (Real.toNNReal s) g x

/-- Quadratic growth bounds for the generator of coordinate displacement powers. -/
theorem gmpPhysical_generator_coordinate_moment_growth {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z x : Vec d) (k : Fin d),
      |physicalGenerator (firstCoordinateIndex hd) ω lam
        (fun y => (y k - z k) ^ 2) x| ≤ C * (1 + |x k - z k| ^ 2) ∧
      |physicalGenerator (firstCoordinateIndex hd) ω lam
        (fun y => (y k - z k) ^ 4) x| ≤
          C * (|x k - z k| ^ 2 + |x k - z k| ^ 4) := by
  obtain ⟨A, B, hA, hB, htwo⟩ :=
    gmpPhysical_generator_coordinate_square_bound hd ω lam Λ hΛ hω hSmooth
  obtain ⟨D, E, hD, hE, hfour⟩ :=
    gmpPhysical_generator_coordinate_fourth_bound hd ω lam Λ hΛ hω hSmooth
  refine ⟨A + B + D + E, by positivity, ?_⟩
  intro z x k
  let u : ℝ := |x k - z k|
  have hu : 0 ≤ u := abs_nonneg _
  have hlin : u ≤ 1 + u ^ 2 := by nlinarith [sq_nonneg (u - 1)]
  have hcub : u ^ 3 ≤ u ^ 2 + u ^ 4 := by
    nlinarith [mul_nonneg (sq_nonneg (u - 1)) (sq_nonneg u)]
  constructor
  · have h := htwo z x k
    change |physicalGenerator _ ω lam (fun y => (y k - z k) ^ 2) x| ≤ A * u + B at h
    calc
      _ ≤ A * u + B := h
      _ ≤ (A + B + D + E) * (1 + u ^ 2) := by
        nlinarith [mul_nonneg hA (sub_nonneg.mpr hlin), sq_nonneg u]
  · have h := hfour z x k
    change |physicalGenerator _ ω lam (fun y => (y k - z k) ^ 4) x| ≤ D * u ^ 3 + E * u ^ 2 at h
    calc
      _ ≤ D * u ^ 3 + E * u ^ 2 := h
      _ ≤ (A + B + D + E) * (u ^ 2 + u ^ 4) := by
        nlinarith [mul_nonneg hD (sub_nonneg.mpr hcub), sq_nonneg u, sq_nonneg (u ^ 2)]

/-- A smooth compact cutoff of an even coordinate displacement power. -/
def gmpPhysicalCoordinateMomentCutoff {d : ℕ} (z : Vec d) (k : Fin d)
    (n : ℕ) (a : ℝ) (y : Vec d) : ℝ :=
  (ContDiffBump.mk (c := (0 : Vec d)) 1 2 one_pos one_lt_two) (a • (y - z)) *
    (y k - z k) ^ (2 * n)

/-- The explicit moment cutoff is compact, smooth, and agrees on the inner ball. -/
theorem gmpPhysical_coordinateMomentCutoff_properties {d : ℕ}
    (z : Vec d) (k : Fin d) (n : ℕ) (a : ℝ) (ha : 0 < a) :
    ContDiff ℝ (⊤ : ℕ∞) (gmpPhysicalCoordinateMomentCutoff z k n a) ∧
      HasCompactSupport (gmpPhysicalCoordinateMomentCutoff z k n a) ∧
      (∀ y, 0 ≤ gmpPhysicalCoordinateMomentCutoff z k n a y ∧
        gmpPhysicalCoordinateMomentCutoff z k n a y ≤ (y k - z k) ^ (2 * n)) ∧
      (∀ y, ‖a • (y - z)‖ ≤ 1 →
        gmpPhysicalCoordinateMomentCutoff z k n a y = (y k - z k) ^ (2 * n)) := by
  let b : ContDiffBump (0 : Vec d) := ⟨1, 2, one_pos, one_lt_two⟩
  let f : Vec d → ℝ := fun y => b (a • (y - z))
  let g : Vec d → ℝ := fun y => (y k - z k) ^ (2 * n)
  have hf : ContDiff ℝ (⊤ : ℕ∞) f :=
    b.contDiff.comp ((contDiff_id.sub contDiff_const).const_smul a)
  have hg : ContDiff ℝ (⊤ : ℕ∞) g :=
    ((contDiff_apply ℝ ℝ k).sub contDiff_const).pow _
  have hc : HasCompactSupport f := by
    simpa [f, sub_eq_add_neg, Function.comp_def] using
      ((b.hasCompactSupport.comp_smul ha.ne').comp_homeomorph (Homeomorph.addRight (-z)))
  change ContDiff ℝ (⊤ : ℕ∞) (fun y => f y * g y) ∧
      HasCompactSupport (fun y => f y * g y) ∧
      (∀ y, 0 ≤ f y * g y ∧ f y * g y ≤ (y k - z k) ^ (2 * n)) ∧
      (∀ y, ‖a • (y - z)‖ ≤ 1 → f y * g y = (y k - z k) ^ (2 * n))
  refine ⟨hf.mul hg, hc.mul_right, ?_, ?_⟩
  · intro y
    have hg0 : 0 ≤ g y := by
      dsimp [g]
      rw [pow_mul]
      exact pow_nonneg (sq_nonneg _) _
    exact ⟨mul_nonneg b.nonneg hg0, by
      simpa [f] using mul_le_mul_of_nonneg_right b.le_one hg0⟩
  · intro y hy
    have hb : f y = 1 := by
      apply b.one_of_mem_closedBall
      simpa [b, dist_zero_right] using hy
    simp [hb, g]

/-- Moment cutoffs at any center and scale are rescalings of a fixed compact test. -/
theorem gmpPhysical_coordinateMomentCutoff_rescale {d : ℕ} (z : Vec d)
    (k : Fin d) (n : ℕ) (a : ℝ) (ha : 0 < a) (y : Vec d) :
    gmpPhysicalCoordinateMomentCutoff z k n a y =
      (a ^ (2 * n))⁻¹ *
        gmpPhysicalCoordinateMomentCutoff 0 k n 1 (a • (y - z)) := by
  simp only [gmpPhysicalCoordinateMomentCutoff, sub_zero, one_smul, Pi.smul_apply,
    smul_eq_mul, Pi.sub_apply, Pi.zero_apply, sub_zero, ← mul_sub, mul_pow]
  field_simp [ne_of_gt ha]
  <;> ring

/-- Compact nonnegative approximants to even coordinate displacement powers. -/
theorem gmpPhysical_coordinateMoment_compact_approximant {d : ℕ}
    (z : Vec d) (k : Fin d) (n : ℕ) (a : ℝ) (ha : 0 < a) :
    ∃ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
      (∀ y, 0 ≤ φ y ∧ φ y ≤ (y k - z k) ^ (2 * n)) ∧
      (∀ y, ‖a • (y - z)‖ ≤ 1 → φ y = (y k - z k) ^ (2 * n)) := by
  let b : ContDiffBump (0 : Vec d) := ⟨1, 2, one_pos, one_lt_two⟩
  let f : Vec d → ℝ := fun y => b (a • (y - z))
  let g : Vec d → ℝ := fun y => (y k - z k) ^ (2 * n)
  have hf : ContDiff ℝ (⊤ : ℕ∞) f :=
    b.contDiff.comp ((contDiff_id.sub contDiff_const).const_smul a)
  have hg : ContDiff ℝ (⊤ : ℕ∞) g :=
    ((contDiff_apply ℝ ℝ k).sub contDiff_const).pow _
  have hc : HasCompactSupport f := by
    simpa [f, sub_eq_add_neg, Function.comp_def] using
      ((b.hasCompactSupport.comp_smul ha.ne').comp_homeomorph (Homeomorph.addRight (-z)))
  refine ⟨fun y => f y * g y, hf.mul hg, hc.mul_right, ?_, ?_⟩
  · intro y
    have hg0 : 0 ≤ g y := by
      dsimp [g]
      rw [pow_mul]
      exact pow_nonneg (sq_nonneg _) _
    exact ⟨mul_nonneg b.nonneg hg0, by
      simpa [f] using mul_le_mul_of_nonneg_right b.le_one hg0⟩
  · intro y hy
    have hb : f y = 1 := by
      apply b.one_of_mem_closedBall
      simpa [b, dist_zero_right] using hy
    simp [hb, g]

/-- A sequence of compact tests eventually agrees pointwise with an even displacement power. -/
theorem gmpPhysical_coordinateMoment_compact_sequence {d : ℕ}
    (z : Vec d) (k : Fin d) (n : ℕ) :
    ∃ φ : ℕ → Vec d → ℝ,
      (∀ m, ContDiff ℝ (⊤ : ℕ∞) (φ m) ∧ HasCompactSupport (φ m)) ∧
      (∀ m y, 0 ≤ φ m y ∧ φ m y ≤ (y k - z k) ^ (2 * n)) ∧
      (∀ y, ∀ᶠ m in atTop, φ m y = (y k - z k) ^ (2 * n)) := by
  let a : ℕ → ℝ := fun m => ((m : ℝ) + 1)⁻¹
  have ha (m : ℕ) : 0 < a m := by dsimp [a]; positivity
  let φ : ℕ → Vec d → ℝ := fun m => gmpPhysicalCoordinateMomentCutoff z k n (a m)
  have hp (m : ℕ) := gmpPhysical_coordinateMomentCutoff_properties z k n (a m) (ha m)
  refine ⟨φ, fun m => ⟨(hp m).1, (hp m).2.1⟩, fun m => (hp m).2.2.1, ?_⟩
  intro y
  have hat : Tendsto a atTop (𝓝 0) := by
    simpa only [a, one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have ht : Tendsto (fun m => a m • (y - z)) atTop (𝓝 (0 : Vec d)) := by
    simpa only [zero_smul] using hat.smul (tendsto_const_nhds (x := y - z))
  have hn : Tendsto (fun m => ‖a m • (y - z)‖) atTop (𝓝 0) := by
    simpa using ht.norm
  have he : ∀ᶠ m in atTop, ‖a m • (y - z)‖ < 1 :=
    hn.eventually (eventually_lt_nhds (by norm_num))
  filter_upwards [he] with m hm
  exact (hp m).2.2.2 y hm.le

/-- Fatou passes uniform compact-test bounds to the full coordinate moment. -/
theorem gmpPhysical_coordinateMoment_compact_fatou {d : ℕ}
    (z : Vec d) (k : Fin d) (n : ℕ) :
    ∃ φ : ℕ → Vec d → ℝ,
      (∀ m, ContDiff ℝ (⊤ : ℕ∞) (φ m) ∧ HasCompactSupport (φ m)) ∧
      (∀ m y, 0 ≤ φ m y ∧ φ m y ≤ (y k - z k) ^ (2 * n)) ∧
      (∀ μ : Measure (Vec d),
        (∫⁻ y, ENNReal.ofReal ((y k - z k) ^ (2 * n)) ∂μ) ≤
          Filter.liminf (fun m => ∫⁻ y, ENNReal.ofReal (φ m y) ∂μ) atTop) := by
  obtain ⟨φ, hs, hb, he⟩ := gmpPhysical_coordinateMoment_compact_sequence z k n
  refine ⟨φ, hs, hb, ?_⟩
  intro μ
  have hm (m : ℕ) : Measurable (fun y => ENNReal.ofReal (φ m y)) :=
    ENNReal.measurable_ofReal.comp (hs m).1.continuous.measurable
  have hl (y : Vec d) : Tendsto (fun m => ENNReal.ofReal (φ m y)) atTop
      (𝓝 (ENNReal.ofReal ((y k - z k) ^ (2 * n)))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [he y] with m hm
    rw [hm]
  calc
    _ = ∫⁻ y, Filter.liminf (fun m => ENNReal.ofReal (φ m y)) atTop ∂μ := by
      apply lintegral_congr
      intro y
      exact (hl y).liminf_eq.symm
    _ ≤ _ := lintegral_liminf_le hm

/-- The full moment is bounded by the liminf of the explicit scaled cutoff integrals. -/
theorem gmpPhysical_coordinateMomentCutoff_fatou {d : ℕ}
    (z : Vec d) (k : Fin d) (n : ℕ) (μ : Measure (Vec d)) :
    (∫⁻ y, ENNReal.ofReal ((y k - z k) ^ (2 * n)) ∂μ) ≤
      Filter.liminf (fun m : ℕ => ∫⁻ y, ENNReal.ofReal
        (gmpPhysicalCoordinateMomentCutoff z k n (((m : ℝ) + 1)⁻¹) y) ∂μ) atTop := by
  let a : ℕ → ℝ := fun m => ((m : ℝ) + 1)⁻¹
  let φ : ℕ → Vec d → ℝ := fun m => gmpPhysicalCoordinateMomentCutoff z k n (a m)
  have ha (m : ℕ) : 0 < a m := by dsimp [a]; positivity
  have hp (m : ℕ) := gmpPhysical_coordinateMomentCutoff_properties z k n (a m) (ha m)
  have hat : Tendsto a atTop (𝓝 0) := by
    simpa only [a, one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hl (y : Vec d) : Tendsto (fun m => ENNReal.ofReal (φ m y)) atTop
      (𝓝 (ENNReal.ofReal ((y k - z k) ^ (2 * n)))) := by
    have ht : Tendsto (fun m => a m • (y - z)) atTop (𝓝 (0 : Vec d)) := by
      simpa only [zero_smul] using hat.smul (tendsto_const_nhds (x := y - z))
    have hn : Tendsto (fun m => ‖a m • (y - z)‖) atTop (𝓝 0) := by
      simpa using ht.norm
    have he : ∀ᶠ m in atTop, ‖a m • (y - z)‖ < 1 :=
      hn.eventually (eventually_lt_nhds (by norm_num))
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with m hm
    change ENNReal.ofReal ((y k - z k) ^ (2 * n)) =
      ENNReal.ofReal (gmpPhysicalCoordinateMomentCutoff z k n (a m) y)
    rw [(hp m).2.2.2 y hm.le]
  have hm (m : ℕ) : Measurable (fun y => ENNReal.ofReal (φ m y)) :=
    ENNReal.measurable_ofReal.comp (hp m).1.continuous.measurable
  change (∫⁻ y, ENNReal.ofReal ((y k - z k) ^ (2 * n)) ∂μ) ≤
    Filter.liminf (fun m => ∫⁻ y, ENNReal.ofReal (φ m y) ∂μ) atTop
  calc
    _ = ∫⁻ y, Filter.liminf (fun m => ENNReal.ofReal (φ m y)) atTop ∂μ := by
      apply lintegral_congr
      intro y
      exact (hl y).liminf_eq.symm
    _ ≤ _ := lintegral_liminf_le hm

/-- First coordinate derivative of a smooth test times a squared displacement. -/
theorem gmpPhysical_coordinateSquare_product_derivative {d : ℕ}
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (z x : Vec d) (k i : Fin d) :
    fderiv ℝ (fun y => f y * (y k - z k) ^ 2) x (unitVector i) =
      (x k - z k) ^ 2 * fderiv ℝ f x (unitVector i) +
        2 * (x k - z k) * f x * (if k = i then 1 else 0) := by
  let q : Vec d → ℝ := fun y => y k - z k
  have hq : ContDiff ℝ (⊤ : ℕ∞) q := (contDiff_apply ℝ ℝ k).sub contDiff_const
  have hdq : fderiv ℝ q x = ContinuousLinearMap.proj k :=
    ((hasFDerivAt_apply (𝕜 := ℝ) k x).sub_const (z k)).fderiv
  change fderiv ℝ (fun y => f y * q y ^ 2) x (unitVector i) = _
  rw [fderiv_fun_mul (hf.differentiable (by simp) x) ((hq.pow 2).differentiable (by simp) x),
    fderiv_fun_pow 2 (hq.differentiable (by simp) x), hdq]
  simp [q, unitVector, Pi.single_apply, mul_comm, mul_left_comm, mul_assoc]
  <;> ring

/-- Second coordinate derivative of a smooth test times a squared displacement. -/
theorem gmpPhysical_coordinateSquare_product_second_derivative {d : ℕ}
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (z x : Vec d) (k i j : Fin d) :
    fderiv ℝ (fun y => fderiv ℝ (fun v => f v * (v k - z k) ^ 2) y (unitVector j)) x (unitVector i) =
      (x k - z k) ^ 2 * fderiv ℝ (fun y => fderiv ℝ f y (unitVector j)) x (unitVector i) +
      2 * (x k - z k) * (if k = i then 1 else 0) * fderiv ℝ f x (unitVector j) +
      2 * (x k - z k) * (if k = j then 1 else 0) * fderiv ℝ f x (unitVector i) +
      2 * f x * (if k = i then 1 else 0) * (if k = j then 1 else 0) := by
  let q : Vec d → ℝ := fun y => y k - z k
  let F : Vec d → ℝ := fun y => fderiv ℝ f y (unitVector j)
  let δ : ℝ := if k = j then 1 else 0
  have hq : ContDiff ℝ (⊤ : ℕ∞) q := (contDiff_apply ℝ ℝ k).sub contDiff_const
  have hF : ContDiff ℝ (⊤ : ℕ∞) F :=
    (contDiff_infty_iff_fderiv.mp hf).2.clm_apply contDiff_const
  have hdq : fderiv ℝ q x = ContinuousLinearMap.proj k :=
    ((hasFDerivAt_apply (𝕜 := ℝ) k x).sub_const (z k)).fderiv
  have he : (fun y => fderiv ℝ (fun v => f v * (v k - z k) ^ 2) y (unitVector j)) =
      (fun y => q y ^ 2 * F y + (2 * δ) * (q y * f y)) := by
    funext y
    rw [gmpPhysical_coordinateSquare_product_derivative f hf z y k j]
    dsimp [q, F, δ]
    ring
  have hfd : DifferentiableAt ℝ f x := hf.differentiable (by simp) x
  have hqd : DifferentiableAt ℝ q x := hq.differentiable (by simp) x
  have hFd : DifferentiableAt ℝ F x := hF.differentiable (by simp) x
  rw [he, fderiv_fun_add, fderiv_fun_mul, fderiv_fun_pow, fderiv_const_mul,
    fderiv_fun_mul, hdq]
  · dsimp [δ]
    split_ifs <;> simp_all [q, F, unitVector, Pi.single_apply] <;> ring
  all_goals fun_prop

/-- Polynomially weighted first and second derivatives of a compact test are uniformly bounded. -/
theorem gmpPhysical_compactTest_weighted_derivative_bounds {d : ℕ} (f : Vec d → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    ∃ B : ℝ, 0 ≤ B ∧
      (∀ x k i, |x k * fderiv ℝ f x (unitVector i)| ≤ B) ∧
      (∀ x k i j, |(x k) ^ 2 *
        fderiv ℝ (fun y => fderiv ℝ f y (unitVector j)) x (unitVector i)| ≤ B) := by
  have hdf (j : Fin d) : ContDiff ℝ (⊤ : ℕ∞)
      (fun y => fderiv ℝ f y (unitVector j)) :=
    (contDiff_infty_iff_fderiv.mp hf).2.clm_apply contDiff_const
  have hcd (j : Fin d) : HasCompactSupport (fun y => fderiv ℝ f y (unitVector j)) :=
    hc.fderiv_apply ℝ (unitVector j)
  have hb (k i : Fin d) : ∃ b : ℝ, ∀ x,
      ‖x k * fderiv ℝ f x (unitVector i)‖ ≤ b := by
    apply (continuous_apply k).mul (hdf i).continuous |>.bounded_above_of_compact_support
    exact (hcd i).mul_left
  have hc' (k i j : Fin d) : ∃ b : ℝ, ∀ x,
      ‖(x k) ^ 2 * fderiv ℝ (fun y => fderiv ℝ f y (unitVector j)) x (unitVector i)‖ ≤ b := by
    apply ((continuous_apply k).pow 2).mul
      ((contDiff_infty_iff_fderiv.mp (hdf j)).2.clm_apply contDiff_const).continuous |>.bounded_above_of_compact_support
    exact ((hcd j).fderiv_apply ℝ (unitVector i)).mul_left
  choose b hb' using hb
  choose c hcBound using hc'
  have hb0 (k i : Fin d) : 0 ≤ b k i := (norm_nonneg _).trans (hb' k i 0)
  have hc0 (k i j : Fin d) : 0 ≤ c k i j := (norm_nonneg _).trans (hcBound k i j 0)
  let B : ℝ := (∑ k, ∑ i, b k i) + ∑ k, ∑ i, ∑ j, c k i j
  have hB1 : 0 ≤ ∑ k, ∑ i, b k i :=
    Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun i _ => hb0 k i
  have hB2 : 0 ≤ ∑ k, ∑ i, ∑ j, c k i j :=
    Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hc0 k i j
  refine ⟨B, add_nonneg hB1 hB2, ?_, ?_⟩
  · intro x k i
    have h := hb' k i x
    rw [Real.norm_eq_abs] at h
    have h1 : b k i ≤ ∑ l, b k l := Finset.single_le_sum (fun l _ => hb0 k l) (Finset.mem_univ i)
    have h2 : (∑ l, b k l) ≤ ∑ k, ∑ l, b k l :=
      Finset.single_le_sum (fun l _ => Finset.sum_nonneg fun m _ => hb0 l m) (Finset.mem_univ k)
    dsimp [B]
    linarith
  · intro x k i j
    have h := hcBound k i j x
    rw [Real.norm_eq_abs] at h
    have h1 : c k i j ≤ ∑ l, c k i l := Finset.single_le_sum (fun l _ => hc0 k i l) (Finset.mem_univ j)
    have h2 : (∑ l, c k i l) ≤ ∑ i, ∑ l, c k i l :=
      Finset.single_le_sum (fun l _ => Finset.sum_nonneg fun m _ => hc0 k l m) (Finset.mem_univ i)
    have h3 : (∑ i, ∑ l, c k i l) ≤ ∑ k, ∑ i, ∑ l, c k i l :=
      Finset.single_le_sum (fun l _ => Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun p _ => hc0 l m p) (Finset.mem_univ k)
    dsimp [B]
    linarith

/-- The unscaled squared cutoff has linear first and bounded second derivatives. -/
theorem gmpPhysical_coordinateSquareCutoff_base_derivative_bounds {d : ℕ} :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (x : Vec d) (k i j : Fin d),
      |fderiv ℝ (gmpPhysicalCoordinateMomentCutoff 0 k 1 1) x (unitVector i)| ≤ B * |x k| ∧
      |fderiv ℝ (fun y => fderiv ℝ (gmpPhysicalCoordinateMomentCutoff 0 k 1 1) y
        (unitVector j)) x (unitVector i)| ≤ B := by
  let b : ContDiffBump (0 : Vec d) := ⟨1, 2, one_pos, one_lt_two⟩
  obtain ⟨D, hD, hfirst, hsecond⟩ :=
    gmpPhysical_compactTest_weighted_derivative_bounds b b.contDiff b.hasCompactSupport
  refine ⟨5 * D + 2, by positivity, ?_⟩
  intro x k i j
  have he : gmpPhysicalCoordinateMomentCutoff 0 k 1 1 = fun y => b y * (y k) ^ 2 := by
    funext y
    simp [gmpPhysicalCoordinateMomentCutoff, b]
  have hb0 : 0 ≤ b x := b.nonneg
  have hb1 : b x ≤ 1 := b.le_one
  have hfirst' := hfirst x k i
  have hfirstj := hfirst x k j
  have hsecond' := hsecond x k i j
  have hxb : 0 ≤ |x k| := abs_nonneg _
  constructor
  · have hd := gmpPhysical_coordinateSquare_product_derivative b b.contDiff 0 x k i
    simp only [Pi.zero_apply, sub_zero] at hd
    rw [he, hd]
    have h1 : |(x k) ^ 2 * fderiv ℝ b x (unitVector i)| ≤ |x k| * D := by
      have heq : |(x k) ^ 2 * fderiv ℝ b x (unitVector i)| =
          |x k| * |x k * fderiv ℝ b x (unitVector i)| := by
        rw [abs_mul, abs_pow, abs_mul]
        ring
      rw [heq]
      exact mul_le_mul_of_nonneg_left hfirst' hxb
    have h2 : |2 * x k * b x * (if k = i then 1 else 0)| ≤ 2 * |x k| := by
      split_ifs <;> simp [abs_mul, abs_of_nonneg hb0] <;> nlinarith
    calc
      _ ≤ |(x k) ^ 2 * fderiv ℝ b x (unitVector i)| +
          |2 * x k * b x * (if k = i then 1 else 0)| := abs_add_le _ _
      _ ≤ _ := by nlinarith [mul_nonneg hD hxb]
  · have hd := gmpPhysical_coordinateSquare_product_second_derivative b b.contDiff 0 x k i j
    simp only [Pi.zero_apply, sub_zero] at hd
    rw [he, hd]
    have h1 : |2 * x k * (if k = i then 1 else 0) * fderiv ℝ b x (unitVector j)| ≤ 2 * D := by
      split_ifs <;> simp [abs_mul] at * <;> nlinarith
    have h2 : |2 * x k * (if k = j then 1 else 0) * fderiv ℝ b x (unitVector i)| ≤ 2 * D := by
      split_ifs <;> simp [abs_mul] at * <;> nlinarith
    have h3 : |2 * b x * (if k = i then 1 else 0) * (if k = j then 1 else 0)| ≤ 2 := by
      split_ifs <;> simp [abs_mul, abs_of_nonneg hb0] <;> nlinarith
    calc
      _ ≤ |(x k) ^ 2 * fderiv ℝ (fun y => fderiv ℝ b y (unitVector j)) x (unitVector i)| +
          |2 * x k * (if k = i then 1 else 0) * fderiv ℝ b x (unitVector j)| +
          |2 * x k * (if k = j then 1 else 0) * fderiv ℝ b x (unitVector i)| +
          |2 * b x * (if k = i then 1 else 0) * (if k = j then 1 else 0)| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_add_le _ _
      _ ≤ _ := by linarith

/-- Derivatives of the squared cutoff inherit the scale-independent base bounds. -/
theorem gmpPhysical_coordinateSquareCutoff_derivative_bounds {d : ℕ} :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (z x : Vec d) (k i j : Fin d) (a : ℝ), 0 < a →
      |fderiv ℝ (gmpPhysicalCoordinateMomentCutoff z k 1 a) x (unitVector i)| ≤
        B * |x k - z k| ∧
      |fderiv ℝ (fun y => fderiv ℝ (gmpPhysicalCoordinateMomentCutoff z k 1 a) y
        (unitVector j)) x (unitVector i)| ≤ B := by
  obtain ⟨B, hB, hb⟩ := gmpPhysical_coordinateSquareCutoff_base_derivative_bounds (d := d)
  refine ⟨B, hB, ?_⟩
  intro z x k i j a ha
  let φ := gmpPhysicalCoordinateMomentCutoff (0 : Vec d) k 1 1
  let ψ : Vec d → ℝ := fun y => φ (a • y)
  let χ : Vec d → ℝ := fun y => ψ (y - z)
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ :=
    (gmpPhysical_coordinateMomentCutoff_properties 0 k 1 1 one_pos).1
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hφ.comp (contDiff_const_smul a)
  have hχ : ContDiff ℝ (⊤ : ℕ∞) χ := hψ.comp (contDiff_id.sub contDiff_const)
  have he : gmpPhysicalCoordinateMomentCutoff z k 1 a = fun y => (a ^ 2)⁻¹ * χ y := by
    funext y
    simpa [χ, ψ, φ] using gmpPhysical_coordinateMomentCutoff_rescale z k 1 a ha y
  have hd (y : Vec d) (l : Fin d) :
      fderiv ℝ (gmpPhysicalCoordinateMomentCutoff z k 1 a) y (unitVector l) =
        (a ^ 2)⁻¹ * fderiv ℝ χ y (unitVector l) := by
    rw [he, fderiv_const_mul]
    · simp only [smul_apply, smul_eq_mul]
    · exact hχ.differentiable (by simp) y
  have hdd :
      fderiv ℝ (fun y => fderiv ℝ (gmpPhysicalCoordinateMomentCutoff z k 1 a) y
        (unitVector j)) x (unitVector i) =
        (a ^ 2)⁻¹ * fderiv ℝ (fun y => fderiv ℝ χ y (unitVector j)) x (unitVector i) := by
    have heq : (fun y => fderiv ℝ (gmpPhysicalCoordinateMomentCutoff z k 1 a) y
        (unitVector j)) = fun y => (a ^ 2)⁻¹ * fderiv ℝ χ y (unitVector j) := by
      funext y
      exact hd y j
    rw [heq, fderiv_const_mul]
    · simp only [smul_apply, smul_eq_mul]
    · exact (((contDiff_infty_iff_fderiv.mp hχ).2.clm_apply contDiff_const).differentiable
        (by simp)) x
  have ht := gmpPhysical_translatedTest_derivatives ψ hψ z x i j
  have hs := gmpPhysical_scaledTest_derivatives φ hφ a (x - z) i j
  have hbase := hb (a • (x - z)) k i j
  have ha0 : 0 ≤ a := ha.le
  have ha2 : 0 ≤ (a ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg a)
  constructor
  · rw [hd, ht.1, hs.1, abs_mul, abs_of_nonneg ha2, abs_mul, abs_of_nonneg ha0]
    have hh := hbase.1
    simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, abs_mul, abs_of_nonneg ha0] at hh
    have hh' := mul_le_mul_of_nonneg_left hh (mul_nonneg ha2 ha0)
    have hc : (a ^ 2)⁻¹ * a * (B * (a * |x k - z k|)) = B * |x k - z k| := by
      field_simp [ne_of_gt ha]
      <;> ring
    nlinarith [hh', hc]
  · rw [hdd, ht.2, hs.2, abs_mul, abs_of_nonneg ha2, abs_mul,
      abs_of_nonneg (sq_nonneg a)]
    have hh := mul_le_mul_of_nonneg_left hbase.2 (mul_nonneg ha2 (sq_nonneg a))
    have hc : (a ^ 2)⁻¹ * a ^ 2 = 1 := inv_mul_cancel₀ (pow_ne_zero _ (ne_of_gt ha))
    nlinarith [hh, hc]

/-- The generator of a squared cutoff grows at most linearly in displacement,
with constants independent of its center and cutoff scale. -/
theorem gmpPhysical_coordinateSquareCutoff_generator_bound {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ (z x : Vec d) (k : Fin d) (a : ℝ), 0 < a →
      |physicalGenerator (firstCoordinateIndex hd) ω lam
        (gmpPhysicalCoordinateMomentCutoff z k 1 a) x| ≤ A * |x k - z k| + B := by
  obtain ⟨D, hD, hderiv⟩ := gmpPhysical_coordinateSquareCutoff_derivative_bounds (d := d)
  obtain ⟨C₁, C₂, hC₁, hC₂, hgen⟩ :=
    gmpPhysical_generator_bound_of_pointwise_derivatives hd ω lam Λ hΛ hω hSmooth
  refine ⟨C₁ * D, C₂ * D, mul_nonneg hC₁ hD, mul_nonneg hC₂ hD, ?_⟩
  intro z x k a ha
  have hs : ContDiff ℝ 2 (gmpPhysicalCoordinateMomentCutoff z k 1 a) :=
    (gmpPhysical_coordinateMomentCutoff_properties z k 1 a ha).1.of_le (by simp)
  have h := hgen _ hs x (D * |x k - z k|) D
    (mul_nonneg hD (abs_nonneg _)) hD
    (fun i => (hderiv z x k i i a ha).1)
    (fun i j => (hderiv z x k i j a ha).2)
  convert h using 1 <;> ring

/-- Integrating the cutoff generator reduces its upper bound to the first
absolute displacement moment of the actual physical kernel. -/
theorem gmpPhysicalC0KernelSemigroup_coordinateSquareCutoff_generator_integral_le
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ (z x : Vec d) (k : Fin d) (a : ℝ), 0 < a → ∀ t : ℝ≥0,
      Integrable (fun y => |y k - z k|)
        (gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x) →
      (∫ y, physicalGenerator (firstCoordinateIndex hd) ω lam
        (gmpPhysicalCoordinateMomentCutoff z k 1 a) y
        ∂(gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x)) ≤
      A * (∫ y, |y k - z k|
        ∂(gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x)) + B := by
  obtain ⟨A, B, hA, hB, hbound⟩ :=
    gmpPhysical_coordinateSquareCutoff_generator_bound hd ω lam Λ hΛ hω hSmooth
  refine ⟨A, B, hA, hB, ?_⟩
  intro z x k a ha t hm
  let P := gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth
  let μ := P t x
  letI : ProbabilityTheory.IsFiniteKernel (P t) := (P.isSubMarkovKernel t).isFiniteKernel
  letI : IsProbabilityMeasure μ := ⟨gmpPhysicalC0KernelSemigroup_conservative hd ω lam Λ hΛ hω hSmooth t x⟩
  have hp := gmpPhysical_coordinateMomentCutoff_properties z k 1 a ha
  have hg : Integrable (physicalGenerator (firstCoordinateIndex hd) ω lam
      (gmpPhysicalCoordinateMomentCutoff z k 1 a)) μ :=
    (EinsteinFull.Work.W5.gantert_contDiff_physicalGenerator _ ω hSmooth lam hp.1).continuous.integrable_of_hasCompactSupport
      (EinsteinFull.Work.W5.gantert_hasCompactSupport_physicalGenerator _ ω lam hp.2.1)
  have hh : Integrable (fun y => A * |y k - z k| + B) μ :=
    (hm.const_mul A).add (integrable_const B)
  have h := integral_mono hg hh (fun y => (abs_le.mp (hbound z y k a ha)).2)
  change (∫ y, physicalGenerator (firstCoordinateIndex hd) ω lam
    (gmpPhysicalCoordinateMomentCutoff z k 1 a) y ∂μ) ≤ _
  calc
    _ ≤ ∫ y, (A * |y k - z k| + B) ∂μ := h
    _ = A * (∫ y, |y k - z k| ∂μ) + B := by
      rw [integral_add (hm.const_mul A) (integrable_const B), integral_const_mul]
      simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
      rfl

/-- A compactly supported smooth approximation to the absolute displacement. -/
def gmpPhysicalCoordinateAbsCutoff {d : ℕ} (z : Vec d) (k : Fin d)
    (a : ℝ) (y : Vec d) : ℝ :=
  (ContDiffBump.mk (c := (0 : Vec d)) 1 2 one_pos one_lt_two) (a • (y - z)) *
    (Real.sqrt (1 + (y k - z k) ^ 2) - 1)

/-- The absolute-displacement cutoff is smooth, compact, and nonnegative. -/
theorem gmpPhysical_coordinateAbsCutoff_properties {d : ℕ}
    (z : Vec d) (k : Fin d) (a : ℝ) (ha : 0 < a) :
    ContDiff ℝ (⊤ : ℕ∞) (gmpPhysicalCoordinateAbsCutoff z k a) ∧
      HasCompactSupport (gmpPhysicalCoordinateAbsCutoff z k a) ∧
      (∀ y, 0 ≤ gmpPhysicalCoordinateAbsCutoff z k a y) ∧
      (∀ y, ‖a • (y - z)‖ ≤ 1 →
        gmpPhysicalCoordinateAbsCutoff z k a y =
          Real.sqrt (1 + (y k - z k) ^ 2) - 1) := by
  let b : ContDiffBump (0 : Vec d) := ⟨1, 2, one_pos, one_lt_two⟩
  let f : Vec d → ℝ := fun y => b (a • (y - z))
  let g : Vec d → ℝ := fun y => Real.sqrt (1 + (y k - z k) ^ 2) - 1
  have hf : ContDiff ℝ (⊤ : ℕ∞) f :=
    b.contDiff.comp ((contDiff_id.sub contDiff_const).const_smul a)
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := by
    apply ContDiff.sub _ contDiff_const
    apply ContDiff.sqrt (contDiff_const.add (((contDiff_apply ℝ ℝ k).sub contDiff_const).pow 2))
    intro y
    positivity
  have hc : HasCompactSupport f := by
    simpa [f, sub_eq_add_neg, Function.comp_def] using
      ((b.hasCompactSupport.comp_smul ha.ne').comp_homeomorph (Homeomorph.addRight (-z)))
  change ContDiff ℝ (⊤ : ℕ∞) (fun y => f y * g y) ∧
    HasCompactSupport (fun y => f y * g y) ∧ (∀ y, 0 ≤ f y * g y) ∧
    (∀ y, ‖a • (y - z)‖ ≤ 1 → f y * g y = g y)
  refine ⟨hf.mul hg, hc.mul_right, ?_, ?_⟩
  · intro y
    apply mul_nonneg b.nonneg
    dsimp [g]
    have h : (1 : ℝ) ≤ Real.sqrt (1 + (y k - z k) ^ 2) := by
      calc
        1 = Real.sqrt 1 := Real.sqrt_one.symm
        _ ≤ Real.sqrt (1 + (y k - z k) ^ 2) :=
          Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg _))
    linarith
  · intro y hy
    have hb : f y = 1 := by
      apply b.one_of_mem_closedBall
      simpa [b, dist_zero_right] using hy
    simp [hb]

/-- The smooth absolute-value approximation differs from the absolute value by at most one. -/
theorem gmpPhysical_smoothAbs_bounds (u : ℝ) :
    0 ≤ Real.sqrt (1 + u ^ 2) - 1 ∧
      Real.sqrt (1 + u ^ 2) - 1 ≤ |u| ∧
      |u| ≤ Real.sqrt (1 + u ^ 2) := by
  have hroot : 0 ≤ Real.sqrt (1 + u ^ 2) := Real.sqrt_nonneg _
  have hsq : (Real.sqrt (1 + u ^ 2)) ^ 2 = 1 + u ^ 2 :=
    Real.sq_sqrt (by positivity)
  have habs : 0 ≤ |u| := abs_nonneg _
  have habssq : |u| ^ 2 = u ^ 2 := sq_abs u
  constructor
  · nlinarith [sq_nonneg u]
  constructor <;> nlinarith

/-- Fatou transfers uniform cutoff estimates to the smooth absolute displacement. -/
theorem gmpPhysical_coordinateAbsCutoff_fatou {d : ℕ}
    (z : Vec d) (k : Fin d) (μ : Measure (Vec d)) :
    (∫⁻ y, ENNReal.ofReal (Real.sqrt (1 + (y k - z k) ^ 2) - 1) ∂μ) ≤
      Filter.liminf (fun m : ℕ => ∫⁻ y, ENNReal.ofReal
        (gmpPhysicalCoordinateAbsCutoff z k (((m : ℝ) + 1)⁻¹) y) ∂μ) atTop := by
  let a : ℕ → ℝ := fun m => ((m : ℝ) + 1)⁻¹
  let φ : ℕ → Vec d → ℝ := fun m => gmpPhysicalCoordinateAbsCutoff z k (a m)
  have ha (m : ℕ) : 0 < a m := by dsimp [a]; positivity
  have hp (m : ℕ) := gmpPhysical_coordinateAbsCutoff_properties z k (a m) (ha m)
  have hat : Tendsto a atTop (𝓝 0) := by
    simpa only [a, one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hl (y : Vec d) : Tendsto (fun m => ENNReal.ofReal (φ m y)) atTop
      (𝓝 (ENNReal.ofReal (Real.sqrt (1 + (y k - z k) ^ 2) - 1))) := by
    have ht : Tendsto (fun m => a m • (y - z)) atTop (𝓝 (0 : Vec d)) := by
      simpa only [zero_smul] using hat.smul (tendsto_const_nhds (x := y - z))
    have hn : Tendsto (fun m => ‖a m • (y - z)‖) atTop (𝓝 0) := by
      simpa using ht.norm
    have he : ∀ᶠ m in atTop, ‖a m • (y - z)‖ < 1 :=
      hn.eventually (eventually_lt_nhds (by norm_num))
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with m hm
    change ENNReal.ofReal (Real.sqrt (1 + (y k - z k) ^ 2) - 1) =
      ENNReal.ofReal (gmpPhysicalCoordinateAbsCutoff z k (a m) y)
    rw [(hp m).2.2.2 y hm.le]
  have hm (m : ℕ) : Measurable (fun y => ENNReal.ofReal (φ m y)) :=
    ENNReal.measurable_ofReal.comp (hp m).1.continuous.measurable
  change (∫⁻ y, ENNReal.ofReal (Real.sqrt (1 + (y k - z k) ^ 2) - 1) ∂μ) ≤
    Filter.liminf (fun m => ∫⁻ y, ENNReal.ofReal (φ m y) ∂μ) atTop
  calc
    _ = ∫⁻ y, Filter.liminf (fun m => ENNReal.ofReal (φ m y)) atTop ∂μ := by
      apply lintegral_congr
      intro y
      exact (hl y).liminf_eq.symm
    _ ≤ _ := lintegral_liminf_le hm

/-- The regularized absolute value has a uniformly bounded first derivative. -/
theorem gmpPhysical_smoothAbs_deriv (u : ℝ) :
    deriv (fun v : ℝ => Real.sqrt (1 + v ^ 2) - 1) u =
      u / Real.sqrt (1 + u ^ 2) ∧
    |deriv (fun v : ℝ => Real.sqrt (1 + v ^ 2) - 1) u| ≤ 1 := by
  have hp : 0 < 1 + u ^ 2 := by positivity
  have hs : 0 < Real.sqrt (1 + u ^ 2) := Real.sqrt_pos.2 hp
  have hd : deriv (fun v : ℝ => Real.sqrt (1 + v ^ 2) - 1) u =
      u / Real.sqrt (1 + u ^ 2) := by
    rw [deriv_sub_const, deriv_sqrt (f := fun v : ℝ => 1 + v ^ 2)
        (by fun_prop) (ne_of_gt hp),
      deriv_const_add, deriv_pow_field]
    norm_num
    ring
  refine ⟨hd, ?_⟩
  rw [hd, abs_div, abs_of_pos hs, div_le_one hs]
  exact (gmpPhysical_smoothAbs_bounds u).2.2

/-- The regularized absolute value also has a uniformly bounded second derivative. -/
theorem gmpPhysical_smoothAbs_second_deriv (u : ℝ) :
    deriv (deriv (fun v : ℝ => Real.sqrt (1 + v ^ 2) - 1)) u =
      1 / (Real.sqrt (1 + u ^ 2)) ^ 3 ∧
    |deriv (deriv (fun v : ℝ => Real.sqrt (1 + v ^ 2) - 1)) u| ≤ 1 := by
  have hp : 0 < 1 + u ^ 2 := by positivity
  have hs : 0 < Real.sqrt (1 + u ^ 2) := Real.sqrt_pos.2 hp
  have hs2 : (Real.sqrt (1 + u ^ 2)) ^ 2 = 1 + u ^ 2 := Real.sq_sqrt hp.le
  have hs1 : 1 ≤ Real.sqrt (1 + u ^ 2) := by
    have h := (gmpPhysical_smoothAbs_bounds u).1
    linarith
  have he : deriv (fun v : ℝ => Real.sqrt (1 + v ^ 2) - 1) =
      fun v => v / Real.sqrt (1 + v ^ 2) := by
    funext v
    exact (gmpPhysical_smoothAbs_deriv v).1
  have hd : deriv (deriv (fun v : ℝ => Real.sqrt (1 + v ^ 2) - 1)) u =
      1 / (Real.sqrt (1 + u ^ 2)) ^ 3 := by
    rw [he, deriv_fun_div (c := fun v : ℝ => v)
        (d := fun v : ℝ => Real.sqrt (1 + v ^ 2)) (by fun_prop)
        ((show DifferentiableAt ℝ (fun v : ℝ => 1 + v ^ 2) u by fun_prop).sqrt (ne_of_gt hp))
        (ne_of_gt hs),
      deriv_id'', deriv_sqrt (f := fun v : ℝ => 1 + v ^ 2)
        (by fun_prop) (ne_of_gt hp), deriv_const_add, deriv_pow_field]
    norm_num
    field_simp
    nlinarith [hs2]
  refine ⟨hd, ?_⟩
  rw [hd, abs_of_nonneg (by positivity), div_le_one (by positivity)]
  nlinarith [sq_nonneg (Real.sqrt (1 + u ^ 2) - 1),
    mul_nonneg (sq_nonneg (Real.sqrt (1 + u ^ 2))) (sub_nonneg.mpr hs1)]

/-- Coordinate derivatives of the regularized absolute displacement are bounded by one. -/
theorem gmpPhysical_coordinateSmoothAbs_derivative_bound {d : ℕ}
    (z x : Vec d) (k i : Fin d) :
    |fderiv ℝ (fun y : Vec d => Real.sqrt (1 + (y k - z k) ^ 2) - 1)
      x (unitVector i)| ≤ 1 := by
  let F : ℝ → ℝ := fun v => Real.sqrt (1 + v ^ 2) - 1
  let q : Vec d → ℝ := fun y => y k - z k
  have hF : DifferentiableAt ℝ F (q x) := by
    dsimp [F]
    apply DifferentiableAt.sub_const
    apply DifferentiableAt.sqrt (by fun_prop)
    positivity
  have hq : HasFDerivAt q (ContinuousLinearMap.proj k) x :=
    (hasFDerivAt_apply (𝕜 := ℝ) k x).sub_const (z k)
  have hd := (hF.hasDerivAt.comp_hasFDerivAt x hq).fderiv
  have he : fderiv ℝ (fun y : Vec d => Real.sqrt (1 + (y k - z k) ^ 2) - 1)
      x (unitVector i) = deriv F (q x) * (if k = i then 1 else 0) := by
    have h := congrArg (fun L : Vec d →L[ℝ] ℝ => L (unitVector i)) hd
    simpa [F, q, Function.comp_def, unitVector, Pi.single_apply, smul_eq_mul] using h
  rw [he]
  split_ifs
  · simpa [F, q] using (gmpPhysical_smoothAbs_deriv (x k - z k)).2
  · simp

/-- Second coordinate derivatives of the regularized displacement are bounded by one. -/
theorem gmpPhysical_coordinateSmoothAbs_second_derivative_bound {d : ℕ}
    (z x : Vec d) (k i j : Fin d) :
    |fderiv ℝ (fun y : Vec d => fderiv ℝ
      (fun v : Vec d => Real.sqrt (1 + (v k - z k) ^ 2) - 1) y (unitVector j))
      x (unitVector i)| ≤ 1 := by
  let F : ℝ → ℝ := fun v => Real.sqrt (1 + v ^ 2) - 1
  let q : Vec d → ℝ := fun y => y k - z k
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := by
    dsimp [F]
    apply ContDiff.sub _ contDiff_const
    apply ContDiff.sqrt (contDiff_const.add (contDiff_id.pow 2))
    intro y
    positivity
  have hF' : Differentiable ℝ (deriv F) :=
    (contDiff_infty_iff_deriv.mp hF).2.differentiable (by simp)
  have hq (y : Vec d) : HasFDerivAt q (ContinuousLinearMap.proj k) y :=
    (hasFDerivAt_apply (𝕜 := ℝ) k y).sub_const (z k)
  have he : (fun y : Vec d => fderiv ℝ
      (fun v : Vec d => Real.sqrt (1 + (v k - z k) ^ 2) - 1) y (unitVector j)) =
      fun y => (if k = j then 1 else 0) * deriv F (q y) := by
    funext y
    have h := (((hF.differentiable (by simp)) (q y)).hasDerivAt.comp_hasFDerivAt y (hq y)).fderiv
    have hh := congrArg (fun L : Vec d →L[ℝ] ℝ => L (unitVector j)) h
    simpa [F, q, Function.comp_def, unitVector, Pi.single_apply, smul_eq_mul, mul_comm] using hh
  rw [he, fderiv_const_mul]
  · have hd := ((hF' (q x)).hasDerivAt.comp_hasFDerivAt x (hq x)).fderiv
    have hh := congrArg (fun L : Vec d →L[ℝ] ℝ => L (unitVector i)) hd
    simp only [ContinuousLinearMap.smul_apply, smul_eq_mul] at hh ⊢
    have hh' : fderiv ℝ (fun y => deriv F (q y)) x (unitVector i) =
        deriv (deriv F) (q x) * (if k = i then 1 else 0) := by
      simpa [Function.comp_def, unitVector, Pi.single_apply, smul_eq_mul] using hh
    rw [hh']
    split_ifs <;> simp only [one_mul, zero_mul, mul_one, mul_zero, abs_zero, zero_le_one]
    simpa [F, q] using (gmpPhysical_smoothAbs_second_deriv (x k - z k)).2
  · exact (hF' (q x)).comp x (hq x).differentiableAt

/-- The physical generator of the regularized coordinate displacement is uniformly bounded. -/
theorem gmpPhysical_coordinateSmoothAbs_generator_bound {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z x : Vec d) (k : Fin d),
      |physicalGenerator (firstCoordinateIndex hd) ω lam
        (fun y : Vec d => Real.sqrt (1 + (y k - z k) ^ 2) - 1) x| ≤ C := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hg⟩ :=
    gmpPhysical_generator_bound_of_pointwise_derivatives hd ω lam Λ hΛ hω hSmooth
  refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, ?_⟩
  intro z x k
  have hs : ContDiff ℝ 2 (fun y : Vec d => Real.sqrt (1 + (y k - z k) ^ 2) - 1) := by
    apply ContDiff.sub _ contDiff_const
    apply ContDiff.sqrt (contDiff_const.add (((contDiff_apply ℝ ℝ k).sub contDiff_const).pow 2))
    intro y
    positivity
  have h := hg _ hs x 1 1 (by norm_num) (by norm_num)
    (fun i => gmpPhysical_coordinateSmoothAbs_derivative_bound z x k i)
    (fun i j => gmpPhysical_coordinateSmoothAbs_second_derivative_bound z x k i j)
  simpa using h

/-- The displacement-weighted first derivative of a scaled bump is scale-independent. -/
theorem gmpPhysical_scaledBump_weighted_derivative_bound {d : ℕ} :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (z x : Vec d) (k i : Fin d) (a : ℝ),
      |(x k - z k) * fderiv ℝ
        (fun y : Vec d => (ContDiffBump.mk (c := (0 : Vec d)) 1 2 one_pos one_lt_two)
          (a • (y - z))) x (unitVector i)| ≤ B := by
  let b : ContDiffBump (0 : Vec d) := ⟨1, 2, one_pos, one_lt_two⟩
  obtain ⟨B, hB, hf, _⟩ :=
    gmpPhysical_compactTest_weighted_derivative_bounds b b.contDiff b.hasCompactSupport
  refine ⟨B, hB, ?_⟩
  intro z x k i a
  let ψ : Vec d → ℝ := fun y => b (a • y)
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := b.contDiff.comp (contDiff_const_smul a)
  have ht := (gmpPhysical_translatedTest_derivatives ψ hψ z x i i).1
  have hs := (gmpPhysical_scaledTest_derivatives b b.contDiff a (x - z) i i).1
  change |(x k - z k) * fderiv ℝ (fun y => ψ (y - z)) x (unitVector i)| ≤ B
  rw [ht, hs]
  have h := hf (a • (x - z)) k i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at h
  convert h using 1 <;> congr 1 <;> ring

/-- A compact smooth test has linearly weighted second derivatives uniformly bounded. -/
theorem gmpPhysical_compactTest_linearWeighted_second_derivative_bound {d : ℕ}
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (x : Vec d) (k i j : Fin d),
      |x k * fderiv ℝ (fun y => fderiv ℝ f y (unitVector j)) x (unitVector i)| ≤ B := by
  obtain ⟨A, hA, _, hsecond⟩ := gmpPhysical_compactTest_derivative_bounds f hf hc
  obtain ⟨D, hD, _, hw⟩ := gmpPhysical_compactTest_weighted_derivative_bounds f hf hc
  refine ⟨A + D, add_nonneg hA hD, ?_⟩
  intro x k i j
  let L : ℝ := fderiv ℝ (fun y => fderiv ℝ f y (unitVector j)) x (unitVector i)
  have hl : |L| ≤ A := hsecond x i j
  have hw' : |(x k) ^ 2 * L| ≤ D := hw x k i j
  have hx : |x k| ≤ 1 + |x k| ^ 2 := by
    nlinarith [sq_nonneg (|x k| - 1)]
  calc
    |x k * L| = |x k| * |L| := abs_mul _ _
    _ ≤ (1 + |x k| ^ 2) * |L| := mul_le_mul_of_nonneg_right hx (abs_nonneg _)
    _ = |L| + |(x k) ^ 2 * L| := by rw [abs_mul, abs_pow]; ring
    _ ≤ A + D := add_le_add hl hw'

/-- The displacement-weighted second derivative of a scaled bump is uniformly bounded. -/
theorem gmpPhysical_scaledBump_weighted_second_derivative_bound {d : ℕ} :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (z x : Vec d) (k i j : Fin d) (a : ℝ), 0 ≤ a → a ≤ 1 →
      |(x k - z k) * fderiv ℝ (fun y => fderiv ℝ
        (fun v : Vec d => (ContDiffBump.mk (c := (0 : Vec d)) 1 2 one_pos one_lt_two)
          (a • (v - z))) y (unitVector j)) x (unitVector i)| ≤ B := by
  let b : ContDiffBump (0 : Vec d) := ⟨1, 2, one_pos, one_lt_two⟩
  obtain ⟨B, hB, hb⟩ :=
    gmpPhysical_compactTest_linearWeighted_second_derivative_bound b b.contDiff b.hasCompactSupport
  refine ⟨B, hB, ?_⟩
  intro z x k i j a ha ha1
  let ψ : Vec d → ℝ := fun y => b (a • y)
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := b.contDiff.comp (contDiff_const_smul a)
  have ht := (gmpPhysical_translatedTest_derivatives ψ hψ z x i j).2
  have hs := (gmpPhysical_scaledTest_derivatives b b.contDiff a (x - z) i j).2
  change |(x k - z k) * fderiv ℝ (fun y => fderiv ℝ
    (fun v => ψ (v - z)) y (unitVector j)) x (unitVector i)| ≤ B
  rw [ht, hs]
  have hh := hb (a • (x - z)) k i j
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at hh
  have he : |(x k - z k) * (a ^ 2 * fderiv ℝ
      (fun y => fderiv ℝ b y (unitVector j)) (a • (x - z)) (unitVector i))| =
      a * |(a * (x k - z k)) * fderiv ℝ
        (fun y => fderiv ℝ b y (unitVector j)) (a • (x - z)) (unitVector i)| := by
    calc
      _ = |a * ((a * (x k - z k)) * fderiv ℝ
          (fun y => fderiv ℝ b y (unitVector j)) (a • (x - z)) (unitVector i))| := by
        congr 1
        ring
      _ = _ := by rw [abs_mul, abs_of_nonneg ha]
  rw [he]
  calc
    _ ≤ a * B := mul_le_mul_of_nonneg_left hh ha
    _ ≤ B := by nlinarith

/-- Coordinate product rules through second order for smooth functions. -/
theorem gmpPhysical_coordinate_product_derivatives {d : ℕ}
    (f g : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (x : Vec d) (i j : Fin d) :
    fderiv ℝ (fun y => f y * g y) x (unitVector i) =
      fderiv ℝ f x (unitVector i) * g x + f x * fderiv ℝ g x (unitVector i) ∧
    fderiv ℝ (fun y => fderiv ℝ (fun v => f v * g v) y (unitVector j)) x (unitVector i) =
      fderiv ℝ (fun y => fderiv ℝ f y (unitVector j)) x (unitVector i) * g x +
      fderiv ℝ f x (unitVector j) * fderiv ℝ g x (unitVector i) +
      fderiv ℝ f x (unitVector i) * fderiv ℝ g x (unitVector j) +
      f x * fderiv ℝ (fun y => fderiv ℝ g y (unitVector j)) x (unitVector i) := by
  have hfirst (y : Vec d) (l : Fin d) :
      fderiv ℝ (fun v => f v * g v) y (unitVector l) =
        fderiv ℝ f y (unitVector l) * g y + f y * fderiv ℝ g y (unitVector l) := by
    rw [fderiv_fun_mul (hf.differentiable (by simp) y) (hg.differentiable (by simp) y)]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  refine ⟨hfirst x i, ?_⟩
  have he : (fun y => fderiv ℝ (fun v => f v * g v) y (unitVector j)) =
      fun y => fderiv ℝ f y (unitVector j) * g y +
        f y * fderiv ℝ g y (unitVector j) := by
    funext y
    exact hfirst y j
  have hdf : Differentiable ℝ (fun y => fderiv ℝ f y (unitVector j)) :=
    ((contDiff_infty_iff_fderiv.mp hf).2.clm_apply contDiff_const).differentiable (by simp)
  have hdg : Differentiable ℝ (fun y => fderiv ℝ g y (unitVector j)) :=
    ((contDiff_infty_iff_fderiv.mp hg).2.clm_apply contDiff_const).differentiable (by simp)
  rw [he, fderiv_fun_add, fderiv_fun_mul, fderiv_fun_mul]
  · simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  all_goals first
    | exact hf.differentiable (by simp) x
    | exact hg.differentiable (by simp) x
    | exact hdf x
    | exact hdg x
    | exact (hdf x).mul (hg.differentiable (by simp) x)
    | exact (hf.differentiable (by simp) x).mul (hdg x)

/-- Scaled bump first derivatives are bounded uniformly for scales at most one. -/
theorem gmpPhysical_scaledBump_derivative_bound {d : ℕ} :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (z x : Vec d) (i : Fin d) (a : ℝ), 0 ≤ a → a ≤ 1 →
      |fderiv ℝ (fun y : Vec d => (ContDiffBump.mk (c := (0 : Vec d))
        1 2 one_pos one_lt_two) (a • (y - z))) x (unitVector i)| ≤ B := by
  let b : ContDiffBump (0 : Vec d) := ⟨1, 2, one_pos, one_lt_two⟩
  obtain ⟨B, hB, hb, _⟩ := gmpPhysical_compactTest_derivative_bounds b b.contDiff b.hasCompactSupport
  refine ⟨B, hB, ?_⟩
  intro z x i a ha ha1
  let ψ : Vec d → ℝ := fun y => b (a • y)
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := b.contDiff.comp (contDiff_const_smul a)
  change |fderiv ℝ (fun y => ψ (y - z)) x (unitVector i)| ≤ B
  rw [(gmpPhysical_translatedTest_derivatives ψ hψ z x i i).1,
    (gmpPhysical_scaledTest_derivatives b b.contDiff a (x - z) i i).1,
    abs_mul, abs_of_nonneg ha]
  calc
    _ ≤ a * B := mul_le_mul_of_nonneg_left (hb (a • (x - z)) i) ha
    _ ≤ B := by nlinarith

/-- The compact absolute-displacement cutoff has uniformly bounded derivatives. -/
theorem gmpPhysical_coordinateAbsCutoff_derivative_bounds {d : ℕ} :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (z x : Vec d) (k i j : Fin d) (a : ℝ), 0 < a → a ≤ 1 →
      |fderiv ℝ (gmpPhysicalCoordinateAbsCutoff z k a) x (unitVector i)| ≤ M ∧
      |fderiv ℝ (fun y => fderiv ℝ (gmpPhysicalCoordinateAbsCutoff z k a) y
        (unitVector j)) x (unitVector i)| ≤ M := by
  obtain ⟨A, hA, hweighted⟩ := gmpPhysical_scaledBump_weighted_derivative_bound (d := d)
  obtain ⟨B, hB, hweighted2⟩ := gmpPhysical_scaledBump_weighted_second_derivative_bound (d := d)
  obtain ⟨D, hD, hfirst⟩ := gmpPhysical_scaledBump_derivative_bound (d := d)
  refine ⟨A + B + 2 * D + 2, by positivity, ?_⟩
  intro z x k i j a ha ha1
  let b : ContDiffBump (0 : Vec d) := ⟨1, 2, one_pos, one_lt_two⟩
  let f : Vec d → ℝ := fun y => b (a • (y - z))
  let g : Vec d → ℝ := fun y => Real.sqrt (1 + (y k - z k) ^ 2) - 1
  have hf : ContDiff ℝ (⊤ : ℕ∞) f :=
    b.contDiff.comp ((contDiff_id.sub contDiff_const).const_smul a)
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := by
    dsimp [g]
    apply ContDiff.sub _ contDiff_const
    apply ContDiff.sqrt (contDiff_const.add (((contDiff_apply ℝ ℝ k).sub contDiff_const).pow 2))
    intro y
    positivity
  have he : gmpPhysicalCoordinateAbsCutoff z k a = fun y => f y * g y := rfl
  have hfx0 : 0 ≤ f x := b.nonneg
  have hfx1 : f x ≤ 1 := b.le_one
  have hgx0 : 0 ≤ g x := (gmpPhysical_smoothAbs_bounds (x k - z k)).1
  have hgx1 : g x ≤ |x k - z k| := (gmpPhysical_smoothAbs_bounds (x k - z k)).2.1
  have hm (v : ℝ) : |v * g x| ≤ |(x k - z k) * v| := by
    rw [abs_mul, abs_of_nonneg hgx0, abs_mul]
    nlinarith [mul_nonneg (abs_nonneg v) (sub_nonneg.mpr hgx1)]
  have hgi : |fderiv ℝ g x (unitVector i)| ≤ 1 :=
    gmpPhysical_coordinateSmoothAbs_derivative_bound z x k i
  have hgj : |fderiv ℝ g x (unitVector j)| ≤ 1 :=
    gmpPhysical_coordinateSmoothAbs_derivative_bound z x k j
  have hgij : |fderiv ℝ (fun y => fderiv ℝ g y (unitVector j)) x (unitVector i)| ≤ 1 :=
    gmpPhysical_coordinateSmoothAbs_second_derivative_bound z x k i j
  have hfi : |fderiv ℝ f x (unitVector i)| ≤ D := hfirst z x i a ha.le ha1
  have hfj : |fderiv ℝ f x (unitVector j)| ≤ D := hfirst z x j a ha.le ha1
  have hfwi : |fderiv ℝ f x (unitVector i) * g x| ≤ A :=
    (hm _).trans (hweighted z x k i a)
  have hfw2 : |fderiv ℝ (fun y => fderiv ℝ f y (unitVector j)) x (unitVector i) * g x| ≤ B :=
    (hm _).trans (hweighted2 z x k i j a ha.le ha1)
  have hbgi : |f x * fderiv ℝ g x (unitVector i)| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hfx0]
    nlinarith [mul_nonneg hfx0 (sub_nonneg.mpr hgi)]
  have hbgij : |f x * fderiv ℝ (fun y => fderiv ℝ g y (unitVector j)) x (unitVector i)| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hfx0]
    nlinarith [mul_nonneg hfx0 (sub_nonneg.mpr hgij)]
  have hcross1 : |fderiv ℝ f x (unitVector j) * fderiv ℝ g x (unitVector i)| ≤ D := by
    rw [abs_mul]
    nlinarith [mul_nonneg (abs_nonneg (fderiv ℝ f x (unitVector j))) (sub_nonneg.mpr hgi)]
  have hcross2 : |fderiv ℝ f x (unitVector i) * fderiv ℝ g x (unitVector j)| ≤ D := by
    rw [abs_mul]
    nlinarith [mul_nonneg (abs_nonneg (fderiv ℝ f x (unitVector i))) (sub_nonneg.mpr hgj)]
  have hp := gmpPhysical_coordinate_product_derivatives f g hf hg x i j
  rw [he, hp.1, hp.2]
  constructor
  · exact (abs_add_le _ _).trans (by linarith)
  · calc
      _ ≤ |fderiv ℝ (fun y => fderiv ℝ f y (unitVector j)) x (unitVector i) * g x| +
          |fderiv ℝ f x (unitVector j) * fderiv ℝ g x (unitVector i)| +
          |fderiv ℝ f x (unitVector i) * fderiv ℝ g x (unitVector j)| +
          |f x * fderiv ℝ (fun y => fderiv ℝ g y (unitVector j)) x (unitVector i)| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_add_le _ _
      _ ≤ _ := by linarith

/-- The physical generator of the compact absolute cutoff is uniformly bounded. -/
theorem gmpPhysical_coordinateAbsCutoff_generator_bound
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z x : Vec d) (k : Fin d) (a : ℝ),
      0 < a → a ≤ 1 →
      |physicalGenerator (firstCoordinateIndex hd) ω lam
        (gmpPhysicalCoordinateAbsCutoff z k a) x| ≤ C := by
  obtain ⟨M, hM, hderiv⟩ := gmpPhysical_coordinateAbsCutoff_derivative_bounds (d := d)
  obtain ⟨C₁, C₂, hC₁, hC₂, hg⟩ :=
    gmpPhysical_generator_bound_of_pointwise_derivatives hd ω lam Λ hΛ hω hSmooth
  refine ⟨C₁ * M + C₂ * M, by positivity, ?_⟩
  intro z x k a ha ha1
  have hs : ContDiff ℝ 2 (gmpPhysicalCoordinateAbsCutoff z k a) :=
    (gmpPhysical_coordinateAbsCutoff_properties z k a ha).1.of_le (by simp)
  exact hg _ hs x M M hM hM (fun i => (hderiv z x k i i a ha ha1).1)
    (fun i j => (hderiv z x k i j a ha ha1).2)

/-- The expected compact absolute displacement has a uniform linear-time bound. -/
theorem gmpPhysicalC0KernelSemigroup_coordinateAbsCutoff_le
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : Vec d) (k : Fin d) (a : ℝ),
      0 < a → a ≤ 1 → ∀ t : ℝ≥0,
      (∫ y, gmpPhysicalCoordinateAbsCutoff x k a y ∂
        (gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x)) ≤ C * (t : ℝ) := by
  obtain ⟨C, hC, hgen⟩ :=
    gmpPhysical_coordinateAbsCutoff_generator_bound hd ω lam Λ hΛ hω hSmooth
  refine ⟨C, hC, ?_⟩
  intro x k a ha ha1 t
  let ψ := gmpPhysicalCoordinateAbsCutoff x k a
  have hp := gmpPhysical_coordinateAbsCutoff_properties x k a ha
  have hn : ‖gmpPhysicalCompactC0 (physicalGenerator (firstCoordinateIndex hd) ω lam ψ)
      (EinsteinFull.Work.W5.gantert_contDiff_physicalGenerator _ ω hSmooth lam hp.1).continuous
      (EinsteinFull.Work.W5.gantert_hasCompactSupport_physicalGenerator _ ω lam hp.2.1)‖ ≤ C := by
    change ‖(gmpPhysicalCompactC0 (physicalGenerator (firstCoordinateIndex hd) ω lam ψ)
      (EinsteinFull.Work.W5.gantert_contDiff_physicalGenerator _ ω hSmooth lam hp.1).continuous
      (EinsteinFull.Work.W5.gantert_hasCompactSupport_physicalGenerator _ ω lam hp.2.1)).toBCF‖ ≤ C
    apply (BoundedContinuousFunction.norm_le hC).2
    intro y
    exact hgen x y k a ha ha1
  have h := gmpPhysicalC0KernelSemigroup_compactTest_sub_le hd ω lam Λ hΛ hω hSmooth ψ hp.1 hp.2.1 t x
  have hz : ψ x = 0 := by simp [ψ, gmpPhysicalCoordinateAbsCutoff]
  rw [hz, sub_zero] at h
  exact (le_abs_self _).trans (h.trans (mul_le_mul_of_nonneg_right hn (NNReal.coe_nonneg t)))

/-- Fatou gives a linear-time bound for the smooth absolute displacement. -/
theorem gmpPhysicalC0KernelSemigroup_smoothAbs_lintegral_le
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : Vec d) (k : Fin d) (t : ℝ≥0),
      (∫⁻ y, ENNReal.ofReal (Real.sqrt (1 + (y k - x k) ^ 2) - 1) ∂
        (gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x)) ≤
          ENNReal.ofReal (C * (t : ℝ)) := by
  obtain ⟨C, hC, hcut⟩ :=
    gmpPhysicalC0KernelSemigroup_coordinateAbsCutoff_le hd ω lam Λ hΛ hω hSmooth
  refine ⟨C, hC, ?_⟩
  intro x k t
  let P := gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth
  let μ := P t x
  letI : ProbabilityTheory.IsFiniteKernel (P t) := (P.isSubMarkovKernel t).isFiniteKernel
  have hb (m : ℕ) :
      (∫⁻ y, ENNReal.ofReal (gmpPhysicalCoordinateAbsCutoff x k (((m : ℝ) + 1)⁻¹) y) ∂μ) ≤
        ENNReal.ofReal (C * (t : ℝ)) := by
    let a : ℝ := ((m : ℝ) + 1)⁻¹
    have ha : 0 < a := by dsimp [a]; positivity
    have ha1 : a ≤ 1 := by
      dsimp [a]
      exact (inv_le_one₀ (by positivity)).2 (by linarith [Nat.cast_nonneg (α := ℝ) m])
    have hp := gmpPhysical_coordinateAbsCutoff_properties x k a ha
    have hi : Integrable (gmpPhysicalCoordinateAbsCutoff x k a) μ :=
      hp.1.continuous.integrable_of_hasCompactSupport hp.2.1
    change (∫⁻ y, ENNReal.ofReal (gmpPhysicalCoordinateAbsCutoff x k a y) ∂μ) ≤ _
    rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ hp.2.2.1)]
    exact ENNReal.ofReal_le_ofReal (hcut x k a ha ha1 t)
  exact (gmpPhysical_coordinateAbsCutoff_fatou x k μ).trans
    (Filter.liminf_le_of_frequently_le' (Filter.Frequently.of_forall hb))

/-- The physical kernel has finite first coordinate moment with a uniform bound. -/
theorem gmpPhysicalC0KernelSemigroup_coordinateAbs_integrable_le
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : Vec d) (k : Fin d) (t : ℝ≥0),
      Integrable (fun y => |y k - x k|)
        (gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x) ∧
      (∫ y, |y k - x k| ∂(gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x)) ≤
        1 + C * (t : ℝ) := by
  obtain ⟨C, hC, hfatou⟩ :=
    gmpPhysicalC0KernelSemigroup_smoothAbs_lintegral_le hd ω lam Λ hΛ hω hSmooth
  refine ⟨C, hC, ?_⟩
  intro x k t
  let P := gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth
  let μ := P t x
  letI : ProbabilityTheory.IsFiniteKernel (P t) := (P.isSubMarkovKernel t).isFiniteKernel
  letI : IsProbabilityMeasure μ := ⟨gmpPhysicalC0KernelSemigroup_conservative hd ω lam Λ hΛ hω hSmooth t x⟩
  let g : Vec d → ℝ := fun y => Real.sqrt (1 + (y k - x k) ^ 2) - 1
  have hgcont : Continuous g := by
    dsimp [g]
    fun_prop
  have hg0 (y : Vec d) : 0 ≤ g y := (gmpPhysical_smoothAbs_bounds (y k - x k)).1
  have hgl : (∫⁻ y, ENNReal.ofReal (g y) ∂μ) ≤ ENNReal.ofReal (C * (t : ℝ)) := hfatou x k t
  have hg : Integrable g μ :=
    (lintegral_ofReal_ne_top_iff_integrable hgcont.aestronglyMeasurable
      (ae_of_all _ hg0)).1 (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hgl)
  have hgint : (∫ y, g y ∂μ) ≤ C * (t : ℝ) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hg (ae_of_all _ hg0)] at hgl
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC (NNReal.coe_nonneg t))).1 hgl
  have ha : Integrable (fun y => |y k - x k|) μ := by
    apply (hg.add (integrable_const 1)).mono_nonneg
      (((continuous_apply k).sub continuous_const).abs.aestronglyMeasurable)
      (ae_of_all _ (fun y => abs_nonneg _))
    exact ae_of_all _ (fun y => by
      dsimp [g]
      linarith [(gmpPhysical_smoothAbs_bounds (y k - x k)).2.2])
  refine ⟨ha, ?_⟩
  have h := integral_mono ha (hg.add (integrable_const 1)) (fun y => by
    dsimp [g]
    linarith [(gmpPhysical_smoothAbs_bounds (y k - x k)).2.2])
  change (∫ y, |y k - x k| ∂μ) ≤ ∫ y, (g y + 1) ∂μ at h
  rw [integral_add hg (integrable_const 1)] at h
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at h
  linarith

/-- The physical kernel has a uniform first absolute coordinate moment. -/
theorem gmpPhysicalC0KernelSemigroup_first_absolute_moment
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ≥0) (x : Vec d) (k : Fin d),
      Integrable (fun y => |y k - x k|)
        (gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x) ∧
      (∫ y, |y k - x k|
        ∂(gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x)) ≤ 1 + C * (t : ℝ) := by
  obtain ⟨C, hC, h⟩ :=
    gmpPhysicalC0KernelSemigroup_coordinateAbs_integrable_le hd ω lam Λ hΛ hω hSmooth
  exact ⟨C, hC, fun t x k => h x k t⟩

/-- The expected square-cutoff generator grows at most linearly in time. -/
theorem gmpPhysicalC0KernelSemigroup_coordinateSquareCutoff_generator_time_bound
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ (x : Vec d) (k : Fin d) (a : ℝ), 0 < a → ∀ t : ℝ≥0,
      (∫ y, physicalGenerator (firstCoordinateIndex hd) ω lam
        (gmpPhysicalCoordinateMomentCutoff x k 1 a) y
        ∂(gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x)) ≤
        A + B * (t : ℝ) := by
  obtain ⟨A, B, hA, hB, hgen⟩ :=
    gmpPhysicalC0KernelSemigroup_coordinateSquareCutoff_generator_integral_le hd ω lam Λ hΛ hω hSmooth
  obtain ⟨C, hC, hm⟩ :=
    gmpPhysicalC0KernelSemigroup_coordinateAbs_integrable_le hd ω lam Λ hΛ hω hSmooth
  refine ⟨A + B, A * C, add_nonneg hA hB, mul_nonneg hA hC, ?_⟩
  intro x k a ha t
  have h := hgen x x k a ha t (hm x k t).1
  have hmul := mul_le_mul_of_nonneg_left (hm x k t).2 hA
  nlinarith

/-- Dynkin's formula bounds the expected compact square displacement. -/
theorem gmpPhysicalC0KernelSemigroup_coordinateSquareCutoff_le
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ (x : Vec d) (k : Fin d) (a : ℝ), 0 < a → ∀ t : ℝ≥0,
      (∫ y, gmpPhysicalCoordinateMomentCutoff x k 1 a y ∂
        (gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x)) ≤
        (A + B * (t : ℝ)) * (t : ℝ) := by
  obtain ⟨A, B, hA, hB, hbound⟩ :=
    gmpPhysicalC0KernelSemigroup_coordinateSquareCutoff_generator_time_bound hd ω lam Λ hΛ hω hSmooth
  refine ⟨A, B, hA, hB, ?_⟩
  intro x k a ha t
  let φ := gmpPhysicalCoordinateMomentCutoff x k 1 a
  have hp := gmpPhysical_coordinateMomentCutoff_properties x k 1 a ha
  let S := gmpPhysicalC0Semigroup hd ω lam Λ hΛ hω hSmooth
  let g := gmpPhysicalCompactC0 (physicalGenerator (firstCoordinateIndex hd) ω lam φ)
      (EinsteinFull.Work.W5.gantert_contDiff_physicalGenerator _ ω hSmooth lam hp.1).continuous
      (EinsteinFull.Work.W5.gantert_hasCompactSupport_physicalGenerator _ ω lam hp.2.1)
  let ev : ZeroAtInftyContinuousMap (Vec d) ℝ →L[ℝ] ℝ :=
    LinearMap.mkContinuous
      { toFun := fun f => f x
        map_add' := by intro f g; rfl
        map_smul' := by intro c f; rfl } 1 (by
          intro f
          simpa using BoundedContinuousFunction.norm_coe_le_norm f.toBCF x)
  have heq (s : ℝ) :
      (∫ y, physicalGenerator (firstCoordinateIndex hd) ω lam φ y ∂
        (gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth (Real.toNNReal s) x)) =
        ev (S (Real.toNNReal s) g) := by
    exact gmpPhysicalC0KernelSemigroup_integral hd ω lam Λ hΛ hω hSmooth (Real.toNNReal s) g x
  have hc : Continuous (fun s : ℝ => ∫ y, physicalGenerator (firstCoordinateIndex hd) ω lam φ y ∂
        (gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth (Real.toNNReal s) x)) := by
    simp_rw [heq]
    exact ev.continuous.comp (S.continuous_operator_toNNReal g)
  have hpoint (s : ℝ) (hs : s ∈ Set.Icc 0 (t : ℝ)) :
      (∫ y, physicalGenerator (firstCoordinateIndex hd) ω lam φ y ∂
        (gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth (Real.toNNReal s) x)) ≤
          A + B * (t : ℝ) := by
    have h := hbound x k a ha (Real.toNNReal s)
    rw [Real.coe_toNNReal' s, max_eq_left hs.1] at h
    exact h.trans (by linarith [mul_le_mul_of_nonneg_left hs.2 hB])
  have hi := intervalIntegral.integral_mono_on (μ := volume) t.coe_nonneg
    (hc.intervalIntegrable 0 t) (intervalIntegrable_const) hpoint
  have hdyn := gmpPhysicalC0KernelSemigroup_compactTest_dynkin hd ω lam Λ hΛ hω hSmooth φ hp.1 hp.2.1 t x
  have hz : φ x = 0 := by simp [φ, gmpPhysicalCoordinateMomentCutoff]
  rw [hz, sub_zero] at hdyn
  rw [hdyn]
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hi
  nlinarith [hi]

/-- The physical kernel has a finite second coordinate displacement moment. -/
theorem gmpPhysicalC0KernelSemigroup_coordinateSquare_integrable_le
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ (x : Vec d) (k : Fin d) (t : ℝ≥0),
      Integrable (fun y => (y k - x k) ^ 2)
        (gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x) ∧
      (∫ y, (y k - x k) ^ 2 ∂(gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x)) ≤
        (A + B * (t : ℝ)) * (t : ℝ) := by
  obtain ⟨A, B, hA, hB, hcut⟩ :=
    gmpPhysicalC0KernelSemigroup_coordinateSquareCutoff_le hd ω lam Λ hΛ hω hSmooth
  refine ⟨A, B, hA, hB, ?_⟩
  intro x k t
  let P := gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth
  let μ := P t x
  letI : ProbabilityTheory.IsFiniteKernel (P t) := (P.isSubMarkovKernel t).isFiniteKernel
  let D : ℝ := (A + B * (t : ℝ)) * (t : ℝ)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hb (m : ℕ) :
      (∫⁻ y, ENNReal.ofReal (gmpPhysicalCoordinateMomentCutoff x k 1 (((m : ℝ) + 1)⁻¹) y) ∂μ) ≤
        ENNReal.ofReal D := by
    let a : ℝ := ((m : ℝ) + 1)⁻¹
    have ha : 0 < a := by dsimp [a]; positivity
    have hp := gmpPhysical_coordinateMomentCutoff_properties x k 1 a ha
    have hi : Integrable (gmpPhysicalCoordinateMomentCutoff x k 1 a) μ :=
      hp.1.continuous.integrable_of_hasCompactSupport hp.2.1
    change (∫⁻ y, ENNReal.ofReal (gmpPhysicalCoordinateMomentCutoff x k 1 a y) ∂μ) ≤ _
    rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun y => (hp.2.2.1 y).1))]
    exact ENNReal.ofReal_le_ofReal (hcut x k a ha t)
  have hl : (∫⁻ y, ENNReal.ofReal ((y k - x k) ^ 2) ∂μ) ≤ ENNReal.ofReal D := by
    have h := (gmpPhysical_coordinateMomentCutoff_fatou x k 1 μ).trans
      (Filter.liminf_le_of_frequently_le' (Filter.Frequently.of_forall hb))
    simpa using h
  have hc : Continuous (fun y : Vec d => (y k - x k) ^ 2) := by fun_prop
  have h0 : ∀ y : Vec d, 0 ≤ (y k - x k) ^ 2 := fun y => sq_nonneg _
  have hint : Integrable (fun y => (y k - x k) ^ 2) μ :=
    (lintegral_ofReal_ne_top_iff_integrable hc.aestronglyMeasurable (ae_of_all _ h0)).1
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hl)
  refine ⟨hint, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ h0)] at hl
  exact (ENNReal.ofReal_le_ofReal_iff hD).1 hl

/-- Squaring a square cutoff gives derivative bounds suited to a fourth-moment bootstrap. -/
theorem gmpPhysical_squaredSquareCutoff_derivative_bounds {d : ℕ} :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (z x : Vec d) (k i j : Fin d) (a : ℝ), 0 < a →
      let f := gmpPhysicalCoordinateMomentCutoff z k 1 a
      |fderiv ℝ (fun y => (f y) ^ 2) x (unitVector i)| ≤
        2 * D * |x k - z k| * f x ∧
      |fderiv ℝ (fun y => fderiv ℝ (fun v => (f v) ^ 2) y (unitVector j)) x (unitVector i)| ≤
        (2 * D + 2 * D ^ 2) * (x k - z k) ^ 2 := by
  obtain ⟨D, hD, hd⟩ := gmpPhysical_coordinateSquareCutoff_derivative_bounds (d := d)
  refine ⟨D, hD, ?_⟩
  intro z x k i j a ha
  let f := gmpPhysicalCoordinateMomentCutoff z k 1 a
  let q : ℝ := x k - z k
  have hp := gmpPhysical_coordinateMomentCutoff_properties z k 1 a ha
  have hf0 : 0 ≤ f x := (hp.2.2.1 x).1
  have hf : f x ≤ q ^ 2 := by simpa [f, q] using (hp.2.2.1 x).2
  have hi : |fderiv ℝ f x (unitVector i)| ≤ D * |q| := (hd z x k i j a ha).1
  have hj : |fderiv ℝ f x (unitVector j)| ≤ D * |q| := (hd z x k j i a ha).1
  have hij : |fderiv ℝ (fun y => fderiv ℝ f y (unitVector j)) x (unitVector i)| ≤ D :=
    (hd z x k i j a ha).2
  have h := gmpPhysical_coordinate_product_derivatives f f hp.1 hp.1 x i j
  change |fderiv ℝ (fun y => f y ^ 2) x (unitVector i)| ≤ _ ∧
    |fderiv ℝ (fun y => fderiv ℝ (fun v => f v ^ 2) y (unitVector j)) x (unitVector i)| ≤ _
  have he : (fun y => f y ^ 2) = fun y => f y * f y := by funext y; ring
  rw [he, h.1, h.2]
  have hp1 := mul_le_mul_of_nonneg_right hi hf0
  have hp2 := mul_le_mul hj hi (abs_nonneg _) (mul_nonneg hD (abs_nonneg q))
  have hp3 := mul_le_mul hij hf hf0 hD
  have htri1 := abs_add_le (fderiv ℝ f x (unitVector i) * f x)
    (f x * fderiv ℝ f x (unitVector i))
  have htri2 := abs_add_le
    (fderiv ℝ (fun y => fderiv ℝ f y (unitVector j)) x (unitVector i) * f x +
      fderiv ℝ f x (unitVector j) * fderiv ℝ f x (unitVector i) +
      fderiv ℝ f x (unitVector i) * fderiv ℝ f x (unitVector j))
    (f x * fderiv ℝ (fun y => fderiv ℝ f y (unitVector j)) x (unitVector i))
  have htri3 := abs_add_le
    (fderiv ℝ (fun y => fderiv ℝ f y (unitVector j)) x (unitVector i) * f x +
      fderiv ℝ f x (unitVector j) * fderiv ℝ f x (unitVector i))
    (fderiv ℝ f x (unitVector i) * fderiv ℝ f x (unitVector j))
  have htri4 := abs_add_le
    (fderiv ℝ (fun y => fderiv ℝ f y (unitVector j)) x (unitVector i) * f x)
    (fderiv ℝ f x (unitVector j) * fderiv ℝ f x (unitVector i))
  simp only [abs_mul, abs_of_nonneg hf0] at htri1 htri2 htri3 htri4
  have hq : |q| ^ 2 = q ^ 2 := sq_abs q
  constructor <;> nlinarith [hp1, hp2, hp3, htri1, htri2, htri3, htri4]

/-- The squared square-cutoff generator is controlled by its value and the square displacement. -/
theorem gmpPhysical_squaredSquareCutoff_generator_bound {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hSmooth : IsSmoothFieldPair ω) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ (z x : Vec d) (k : Fin d) (a : ℝ), 0 < a →
      let f := gmpPhysicalCoordinateMomentCutoff z k 1 a
      |physicalGenerator (firstCoordinateIndex hd) ω lam (fun y => (f y) ^ 2) x| ≤
        A * (x k - z k) ^ 2 + B * (f x) ^ 2 := by
  obtain ⟨D, hD, hderiv⟩ := gmpPhysical_squaredSquareCutoff_derivative_bounds (d := d)
  obtain ⟨C₁, C₂, hC₁, hC₂, hg⟩ :=
    gmpPhysical_generator_bound_of_pointwise_derivatives hd ω lam Λ hΛ hω hSmooth
  refine ⟨C₁ * D + C₂ * (2 * D + 2 * D ^ 2), C₁ * D, by positivity, by positivity, ?_⟩
  intro z x k a ha
  let f := gmpPhysicalCoordinateMomentCutoff z k 1 a
  let q : ℝ := x k - z k
  have hs : ContDiff ℝ 2 (fun y => (f y) ^ 2) :=
    ((gmpPhysical_coordinateMomentCutoff_properties z k 1 a ha).1.pow 2).of_le (by simp)
  have hfirst (i : Fin d) :
      |fderiv ℝ (fun y => (f y) ^ 2) x (unitVector i)| ≤ D * (q ^ 2 + (f x) ^ 2) := by
    have h := (hderiv z x k i i a ha).1
    have hq : |q| ^ 2 = q ^ 2 := sq_abs q
    nlinarith [sq_nonneg (|q| - f x), mul_nonneg hD (sq_nonneg (|q| - f x))]
  have hsecond (i j : Fin d) :
      |fderiv ℝ (fun y => fderiv ℝ (fun v => (f v) ^ 2) y (unitVector j)) x (unitVector i)| ≤
        (2 * D + 2 * D ^ 2) * q ^ 2 := (hderiv z x k i j a ha).2
  have h := hg _ hs x (D * (q ^ 2 + (f x) ^ 2)) ((2 * D + 2 * D ^ 2) * q ^ 2)
    (by positivity) (by positivity) hfirst hsecond
  convert h using 1 <;> dsimp [q] <;> ring

/-- Integrating the fourth-cutoff generator uses the established second moment. -/
theorem gmpPhysicalC0KernelSemigroup_squaredSquareCutoff_generator_integral_le
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ (x : Vec d) (k : Fin d) (a : ℝ), 0 < a → ∀ t : ℝ≥0,
      let f := gmpPhysicalCoordinateMomentCutoff x k 1 a
      (∫ y, physicalGenerator (firstCoordinateIndex hd) ω lam (fun v => (f v) ^ 2) y ∂
        (gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x)) ≤
      A * (∫ y, (y k - x k) ^ 2 ∂(gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x)) +
      B * (∫ y, (f y) ^ 2 ∂(gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x)) := by
  obtain ⟨A, B, hA, hB, hgen⟩ :=
    gmpPhysical_squaredSquareCutoff_generator_bound hd ω lam Λ hΛ hω hSmooth
  obtain ⟨C, D, hC, hD, hm⟩ :=
    gmpPhysicalC0KernelSemigroup_coordinateSquare_integrable_le hd ω lam Λ hΛ hω hSmooth
  refine ⟨A, B, hA, hB, ?_⟩
  intro x k a ha t
  let P := gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth
  let μ := P t x
  letI : ProbabilityTheory.IsFiniteKernel (P t) := (P.isSubMarkovKernel t).isFiniteKernel
  let f := gmpPhysicalCoordinateMomentCutoff x k 1 a
  have hp := gmpPhysical_coordinateMomentCutoff_properties x k 1 a ha
  have hfs : ContDiff ℝ (⊤ : ℕ∞) (fun y => (f y) ^ 2) := hp.1.pow 2
  have hfc : HasCompactSupport (fun y => (f y) ^ 2) := by
    have hh : HasCompactSupport (fun y => f y * f y) := hp.2.1.mul_right
    simpa only [pow_two] using hh
  have hf : Integrable (fun y => (f y) ^ 2) μ := hfs.continuous.integrable_of_hasCompactSupport hfc
  have hg : Integrable (physicalGenerator (firstCoordinateIndex hd) ω lam (fun y => (f y) ^ 2)) μ :=
    (EinsteinFull.Work.W5.gantert_contDiff_physicalGenerator _ ω hSmooth lam hfs).continuous.integrable_of_hasCompactSupport
      (EinsteinFull.Work.W5.gantert_hasCompactSupport_physicalGenerator _ ω lam hfc)
  have hq := (hm x k t).1
  have hh : Integrable (fun y => A * (y k - x k) ^ 2 + B * (f y) ^ 2) μ :=
    (hq.const_mul A).add (hf.const_mul B)
  have h := integral_mono hg hh (fun y => (abs_le.mp (hgen x y k a ha)).2)
  rw [integral_add (hq.const_mul A) (hf.const_mul B), integral_const_mul, integral_const_mul] at h
  exact h


/-- Dynkin's formula gives a closed integral inequality for the fourth cutoff. -/
theorem gmpPhysicalC0KernelSemigroup_squaredSquareCutoff_integral_inequality
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) :
    ∃ A B C : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ C ∧
      ∀ (x : Vec d) (k : Fin d) (a : ℝ), 0 < a → ∀ t : ℝ≥0,
      let f := gmpPhysicalCoordinateMomentCutoff x k 1 a
      (∫ y, (f y) ^ 2 ∂(gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x)) ≤
        (A + B * (t : ℝ)) * (t : ℝ) ^ 2 +
        C * ∫ s in (0 : ℝ)..(t : ℝ),
          ∫ y, (f y) ^ 2 ∂(gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth (Real.toNNReal s) x) := by
  obtain ⟨A, B, hA, hB, hgen⟩ :=
    gmpPhysicalC0KernelSemigroup_squaredSquareCutoff_generator_integral_le hd ω lam Λ hΛ hω hSmooth
  obtain ⟨D, E, hD, hE, hmoment⟩ :=
    gmpPhysicalC0KernelSemigroup_coordinateSquare_integrable_le hd ω lam Λ hΛ hω hSmooth
  refine ⟨A * D, A * E, B, by positivity, by positivity, hB, ?_⟩
  intro x k a ha t
  let f := gmpPhysicalCoordinateMomentCutoff x k 1 a
  let φ : Vec d → ℝ := fun y => (f y) ^ 2
  have hp := gmpPhysical_coordinateMomentCutoff_properties x k 1 a ha
  have hs : ContDiff ℝ (⊤ : ℕ∞) φ := hp.1.pow 2
  have hcompact : HasCompactSupport φ := by
    have h : HasCompactSupport (fun y => f y * f y) := hp.2.1.mul_right
    simpa only [φ, pow_two] using h
  let S := gmpPhysicalC0Semigroup hd ω lam Λ hΛ hω hSmooth
  let ev : ZeroAtInftyContinuousMap (Vec d) ℝ →L[ℝ] ℝ :=
    LinearMap.mkContinuous
      { toFun := fun g => g x
        map_add' := by intro g h; rfl
        map_smul' := by intro c g; rfl } 1 (by
          intro g
          simpa using BoundedContinuousFunction.norm_coe_le_norm g.toBCF x)
  let F := gmpPhysicalCompactC0 φ hs.continuous hcompact
  let G := gmpPhysicalCompactC0 (physicalGenerator (firstCoordinateIndex hd) ω lam φ)
    (EinsteinFull.Work.W5.gantert_contDiff_physicalGenerator _ ω hSmooth lam hs).continuous
    (EinsteinFull.Work.W5.gantert_hasCompactSupport_physicalGenerator _ ω lam hcompact)
  have hcF : Continuous (fun s : ℝ => ∫ y, φ y ∂
      (gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth (Real.toNNReal s) x)) := by
    have heq (s : ℝ) : (∫ y, φ y ∂
        (gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth (Real.toNNReal s) x)) =
          ev (S (Real.toNNReal s) F) :=
      gmpPhysicalC0KernelSemigroup_integral hd ω lam Λ hΛ hω hSmooth (Real.toNNReal s) F x
    simp_rw [heq]
    exact ev.continuous.comp (S.continuous_operator_toNNReal F)
  have hcG : Continuous (fun s : ℝ => ∫ y, physicalGenerator (firstCoordinateIndex hd) ω lam φ y ∂
      (gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth (Real.toNNReal s) x)) := by
    have heq (s : ℝ) : (∫ y, physicalGenerator (firstCoordinateIndex hd) ω lam φ y ∂
        (gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth (Real.toNNReal s) x)) =
          ev (S (Real.toNNReal s) G) :=
      gmpPhysicalC0KernelSemigroup_integral hd ω lam Λ hΛ hω hSmooth (Real.toNNReal s) G x
    simp_rw [heq]
    exact ev.continuous.comp (S.continuous_operator_toNNReal G)
  have hpoint (s : ℝ) (hsi : s ∈ Set.Icc 0 (t : ℝ)) :
      (∫ y, physicalGenerator (firstCoordinateIndex hd) ω lam φ y ∂
        (gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth (Real.toNNReal s) x)) ≤
      A * ((D + E * (t : ℝ)) * (t : ℝ)) + B * (∫ y, φ y ∂
        (gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth (Real.toNNReal s) x)) := by
    have h := hgen x k a ha (Real.toNNReal s)
    have hm := (hmoment x k (Real.toNNReal s)).2
    rw [Real.coe_toNNReal' s, max_eq_left hsi.1] at hm
    have hpoly : (D + E * s) * s ≤ (D + E * (t : ℝ)) * (t : ℝ) := by
      nlinarith [mul_nonneg hE hsi.1, mul_nonneg hE t.coe_nonneg,
        mul_nonneg (sub_nonneg.mpr hsi.2) hD,
        mul_nonneg (sub_nonneg.mpr hsi.2) (mul_nonneg hE (add_nonneg hsi.1 t.coe_nonneg))]
    have hh := mul_le_mul_of_nonneg_left (hm.trans hpoly) hA
    dsimp [φ, f] at h ⊢
    linarith
  have hi := intervalIntegral.integral_mono_on (μ := volume) t.coe_nonneg
    (hcG.intervalIntegrable 0 t)
    ((intervalIntegrable_const).add ((hcF.intervalIntegrable 0 t).const_mul B)) hpoint
  have hdyn := gmpPhysicalC0KernelSemigroup_compactTest_dynkin hd ω lam Λ hΛ hω hSmooth φ hs hcompact t x
  have hz : φ x = 0 := by simp [φ, f, gmpPhysicalCoordinateMomentCutoff]
  rw [hz, sub_zero] at hdyn
  change (∫ y, φ y ∂(gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x)) ≤ _
  rw [hdyn]
  rw [intervalIntegral.integral_add (intervalIntegrable_const) ((hcF.intervalIntegrable 0 t).const_mul B),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul] at hi
  simp only [smul_eq_mul, sub_zero] at hi
  nlinarith [hi]


/-- Fatou's lemma removes the cutoff from squared square displacements. -/
theorem gmpPhysical_squaredSquareCutoff_fatou {d : ℕ}
    (z : Vec d) (k : Fin d) (μ : Measure (Vec d)) :
    (∫⁻ y, ENNReal.ofReal ((y k - z k) ^ 4) ∂μ) ≤
      Filter.liminf (fun m : ℕ => ∫⁻ y, ENNReal.ofReal
        ((gmpPhysicalCoordinateMomentCutoff z k 1 (((m : ℝ) + 1)⁻¹) y) ^ 2) ∂μ) atTop := by
  let a : ℕ → ℝ := fun m => ((m : ℝ) + 1)⁻¹
  let φ : ℕ → Vec d → ℝ := fun m => (gmpPhysicalCoordinateMomentCutoff z k 1 (a m) ·) ^ 2
  have ha (m : ℕ) : 0 < a m := by dsimp [a]; positivity
  have hp (m : ℕ) := gmpPhysical_coordinateMomentCutoff_properties z k 1 (a m) (ha m)
  have hat : Tendsto a atTop (𝓝 0) := by
    simpa only [a, one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hl (y : Vec d) : Tendsto (fun m => ENNReal.ofReal (φ m y)) atTop
      (𝓝 (ENNReal.ofReal ((y k - z k) ^ 4))) := by
    have ht : Tendsto (fun m => a m • (y - z)) atTop (𝓝 (0 : Vec d)) := by
      simpa only [zero_smul] using hat.smul (tendsto_const_nhds (x := y - z))
    have hn : Tendsto (fun m => ‖a m • (y - z)‖) atTop (𝓝 0) := by
      simpa using ht.norm
    have he : ∀ᶠ m in atTop, ‖a m • (y - z)‖ < 1 :=
      hn.eventually (eventually_lt_nhds (by norm_num))
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with m hm
    change ENNReal.ofReal ((y k - z k) ^ 4) =
      ENNReal.ofReal ((gmpPhysicalCoordinateMomentCutoff z k 1 (a m) y) ^ 2)
    rw [(hp m).2.2.2 y hm.le]
    congr 1
    ring
  have hm (m : ℕ) : Measurable (fun y => ENNReal.ofReal (φ m y)) :=
    ENNReal.measurable_ofReal.comp ((hp m).1.pow 2).continuous.measurable
  change (∫⁻ y, ENNReal.ofReal ((y k - z k) ^ 4) ∂μ) ≤
    Filter.liminf (fun m => ∫⁻ y, ENNReal.ofReal (φ m y) ∂μ) atTop
  calc
    _ = ∫⁻ y, Filter.liminf (fun m => ENNReal.ofReal (φ m y)) atTop ∂μ := by
      apply lintegral_congr
      intro y
      exact (hl y).liminf_eq.symm
    _ ≤ _ := lintegral_liminf_le hm


/-- A small-time integral inequality yields a quadratic bound via the interval maximum. -/
theorem gmpPhysical_quadratic_bound_of_integral_inequality
    (f : ℝ → ℝ) (hf : Continuous f) (A B C : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ f t)
    (hineq : ∀ t, 0 ≤ t → f t ≤ (A + B * t) * t ^ 2 + C * ∫ s in (0 : ℝ)..t, f s) :
    ∀ t, 0 ≤ t → t ≤ (2 * (C + 1))⁻¹ → f t ≤ 2 * (A + B) * t ^ 2 := by
  let δ : ℝ := (2 * (C + 1))⁻¹
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδone : δ ≤ 1 := by
    dsimp [δ]
    rw [inv_le_one₀ (by positivity)]
    linarith
  have hCδ : C * δ ≤ 1 / 2 := by
    dsimp [δ]
    have hpos : 0 < 2 * (C + 1) := by positivity
    rw [mul_inv_le_iff₀ hpos]
    linarith
  intro t ht htδ
  change t ≤ δ at htδ
  obtain ⟨u, hu, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr ht) hf.continuousOn
  have hfu : 0 ≤ f u := hnonneg u hu.1
  have hft : f t ≤ f u := hmax ⟨ht, le_rfl⟩
  have hInt := intervalIntegral.integral_mono_on (μ := volume) hu.1
    (hf.intervalIntegrable 0 u) intervalIntegrable_const (fun s hs => hmax ⟨hs.1, hs.2.trans hu.2⟩)
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hInt
  have hA' : A + B * u ≤ A + B := by
    have : u ≤ 1 := hu.2.trans (htδ.trans hδone)
    nlinarith
  have hp : (A + B * u) * u ^ 2 ≤ (A + B) * t ^ 2 := by
    have hsq : u ^ 2 ≤ t ^ 2 := by nlinarith [hu.1, hu.2, ht]
    have ha0 : 0 ≤ A + B * u := add_nonneg hA (mul_nonneg hB hu.1)
    nlinarith [mul_nonneg (sub_nonneg.mpr hA') (sq_nonneg u),
      mul_nonneg (add_nonneg hA hB) (sub_nonneg.mpr hsq)]
  have hCt : C * u ≤ 1 / 2 := by
    nlinarith [mul_nonneg hC (sub_nonneg.mpr (hu.2.trans htδ))]
  have h := hineq u hu.1
  have hi := mul_le_mul_of_nonneg_left hInt hC
  nlinarith [mul_nonneg (sub_nonneg.mpr hCt) hfu]


/-- Squared square-cutoff expectations have a uniform quadratic bound at small times. -/
theorem gmpPhysicalC0KernelSemigroup_squaredSquareCutoff_local_le
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ (x : Vec d) (k : Fin d) (a : ℝ), 0 < a →
      ∀ t : ℝ≥0, (t : ℝ) ≤ δ →
      (∫ y, (gmpPhysicalCoordinateMomentCutoff x k 1 a y) ^ 2 ∂
        (gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x)) ≤ C * (t : ℝ) ^ 2 := by
  obtain ⟨A, B, D, hA, hB, hD, hineq⟩ :=
    gmpPhysicalC0KernelSemigroup_squaredSquareCutoff_integral_inequality hd ω lam Λ hΛ hω hSmooth
  refine ⟨2 * (A + B), (2 * (D + 1))⁻¹, by positivity, by positivity, ?_⟩
  intro x k a ha t ht
  let f := gmpPhysicalCoordinateMomentCutoff x k 1 a
  let φ : Vec d → ℝ := fun y => (f y) ^ 2
  have hp := gmpPhysical_coordinateMomentCutoff_properties x k 1 a ha
  have hs : ContDiff ℝ (⊤ : ℕ∞) φ := hp.1.pow 2
  have hcompact : HasCompactSupport φ := by
    have h : HasCompactSupport (fun y => f y * f y) := hp.2.1.mul_right
    simpa only [φ, pow_two] using h
  let S := gmpPhysicalC0Semigroup hd ω lam Λ hΛ hω hSmooth
  let F := gmpPhysicalCompactC0 φ hs.continuous hcompact
  let ev : ZeroAtInftyContinuousMap (Vec d) ℝ →L[ℝ] ℝ :=
    LinearMap.mkContinuous
      { toFun := fun g => g x
        map_add' := by intro g h; rfl
        map_smul' := by intro c g; rfl } 1 (by
          intro g
          simpa using BoundedContinuousFunction.norm_coe_le_norm g.toBCF x)
  let m : ℝ → ℝ := fun s => ∫ y, φ y ∂
    (gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth (Real.toNNReal s) x)
  have hc : Continuous m := by
    have heq (s : ℝ) : m s = ev (S (Real.toNNReal s) F) :=
      gmpPhysicalC0KernelSemigroup_integral hd ω lam Λ hΛ hω hSmooth (Real.toNNReal s) F x
    rw [funext heq]
    exact ev.continuous.comp (S.continuous_operator_toNNReal F)
  have hnonneg (s : ℝ) (_ : 0 ≤ s) : 0 ≤ m s := by
    apply integral_nonneg
    intro y
    exact sq_nonneg _
  have hi (s : ℝ) (hs0 : 0 ≤ s) :
      m s ≤ (A + B * s) * s ^ 2 + D * ∫ r in (0 : ℝ)..s, m r := by
    have h := hineq x k a ha (Real.toNNReal s)
    rw [Real.coe_toNNReal' s, max_eq_left hs0] at h
    exact h
  have h := gmpPhysical_quadratic_bound_of_integral_inequality m hc A B D hA hB hD hnonneg hi t t.coe_nonneg ht
  simpa [m, φ, f] using h


/-- The physical kernel has a locally quadratic fourth coordinate moment. -/
theorem gmpPhysicalC0KernelSemigroup_coordinateFourth_local_integrable_le
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ (x : Vec d) (k : Fin d) (t : ℝ≥0),
      (t : ℝ) ≤ δ →
      Integrable (fun y => (y k - x k) ^ 4)
        (gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x) ∧
      (∫ y, (y k - x k) ^ 4 ∂(gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x)) ≤
        C * (t : ℝ) ^ 2 := by
  obtain ⟨C, δ, hC, hδ, hcut⟩ :=
    gmpPhysicalC0KernelSemigroup_squaredSquareCutoff_local_le hd ω lam Λ hΛ hω hSmooth
  refine ⟨C, δ, hC, hδ, ?_⟩
  intro x k t ht
  let P := gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth
  let μ := P t x
  letI : ProbabilityTheory.IsFiniteKernel (P t) := (P.isSubMarkovKernel t).isFiniteKernel
  let D : ℝ := C * (t : ℝ) ^ 2
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hb (m : ℕ) :
      (∫⁻ y, ENNReal.ofReal ((gmpPhysicalCoordinateMomentCutoff x k 1 (((m : ℝ) + 1)⁻¹) y) ^ 2) ∂μ) ≤
        ENNReal.ofReal D := by
    let a : ℝ := ((m : ℝ) + 1)⁻¹
    have ha : 0 < a := by dsimp [a]; positivity
    have hp := gmpPhysical_coordinateMomentCutoff_properties x k 1 a ha
    have hc : HasCompactSupport (fun y => (gmpPhysicalCoordinateMomentCutoff x k 1 a y) ^ 2) := by
      have hh : HasCompactSupport (fun y => gmpPhysicalCoordinateMomentCutoff x k 1 a y *
          gmpPhysicalCoordinateMomentCutoff x k 1 a y) := hp.2.1.mul_right
      simpa only [pow_two] using hh
    have hi : Integrable (fun y => (gmpPhysicalCoordinateMomentCutoff x k 1 a y) ^ 2) μ :=
      (hp.1.pow 2).continuous.integrable_of_hasCompactSupport hc
    change (∫⁻ y, ENNReal.ofReal ((gmpPhysicalCoordinateMomentCutoff x k 1 a y) ^ 2) ∂μ) ≤ _
    rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun y => sq_nonneg _))]
    exact ENNReal.ofReal_le_ofReal (hcut x k a ha t ht)
  have hl : (∫⁻ y, ENNReal.ofReal ((y k - x k) ^ 4) ∂μ) ≤ ENNReal.ofReal D := by
    exact (gmpPhysical_squaredSquareCutoff_fatou x k μ).trans
      (Filter.liminf_le_of_frequently_le' (Filter.Frequently.of_forall hb))
  have hc : Continuous (fun y : Vec d => (y k - x k) ^ 4) := by fun_prop
  have h0 : ∀ y : Vec d, 0 ≤ (y k - x k) ^ 4 := fun y => by positivity
  have hint : Integrable (fun y => (y k - x k) ^ 4) μ :=
    (lintegral_ofReal_ne_top_iff_integrable hc.aestronglyMeasurable (ae_of_all _ h0)).1
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hl)
  refine ⟨hint, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ h0)] at hl
  exact (ENNReal.ofReal_le_ofReal_iff hD).1 hl


/-- The fourth power of Euclidean displacement is controlled by coordinate fourth powers. -/
theorem gmpPhysical_sum_coordinateSquares_sq_le {d : ℕ} (x y : Vec d) :
    (∑ k : Fin d, (y k - x k) ^ 2) ^ 2 ≤
      (d : ℝ) * ∑ k : Fin d, (y k - x k) ^ 4 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : Fin d => (1 : ℝ)) (fun k : Fin d => (y k - x k) ^ 2)
  simpa only [one_mul, one_pow, Finset.sum_const_zero, Finset.sum_const,
    Finset.card_fin, nsmul_eq_mul, mul_one, ← pow_mul] using h

/-- The actual Euclidean fourth displacement moment is locally quadratic in time. -/
theorem gmpPhysicalC0KernelSemigroup_euclideanFourth_local_integrable_le
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ (x : Vec d) (t : ℝ≥0), (t : ℝ) ≤ δ →
      Integrable (fun y => (∑ k : Fin d, (y k - x k) ^ 2) ^ 2)
        (gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x) ∧
      (∫ y, (∑ k : Fin d, (y k - x k) ^ 2) ^ 2 ∂
        (gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x)) ≤ C * (t : ℝ) ^ 2 := by
  obtain ⟨C, δ, hC, hδ, hm⟩ :=
    gmpPhysicalC0KernelSemigroup_coordinateFourth_local_integrable_le hd ω lam Λ hΛ hω hSmooth
  refine ⟨(d : ℝ) ^ 2 * C, δ, by positivity, hδ, ?_⟩
  intro x t ht
  let μ := gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x
  have hi (k : Fin d) : Integrable (fun y => (y k - x k) ^ 4) μ := (hm x k t ht).1
  have hsum : Integrable (fun y => ∑ k : Fin d, (y k - x k) ^ 4) μ :=
    integrable_finsetSum _ (fun k _ => hi k)
  have hcont : Continuous (fun y : Vec d => (∑ k : Fin d, (y k - x k) ^ 2) ^ 2) := by fun_prop
  have hdom : Integrable (fun y => (d : ℝ) * ∑ k : Fin d, (y k - x k) ^ 4) μ :=
    hsum.const_mul (d : ℝ)
  have htarget : Integrable (fun y => (∑ k : Fin d, (y k - x k) ^ 2) ^ 2) μ :=
    hdom.mono_nonneg hcont.aestronglyMeasurable (ae_of_all _ (fun y => sq_nonneg _))
      (ae_of_all _ (gmpPhysical_sum_coordinateSquares_sq_le x))
  refine ⟨htarget, ?_⟩
  have h := integral_mono htarget hdom (gmpPhysical_sum_coordinateSquares_sq_le x)
  rw [integral_const_mul, integral_finsetSum _ (fun k _ => hi k)] at h
  have hsumle : (∑ k : Fin d, ∫ y, (y k - x k) ^ 4 ∂μ) ≤
      (d : ℝ) * (C * (t : ℝ) ^ 2) := by
    calc
      _ ≤ ∑ _k : Fin d, C * (t : ℝ) ^ 2 := Finset.sum_le_sum (fun k _ => (hm x k t ht).2)
      _ = _ := by simp
  have hh := mul_le_mul_of_nonneg_left hsumle (show (0 : ℝ) ≤ d by positivity)
  nlinarith [h, hh]


/-- The local bound written using the explicit Euclidean norm of the project. -/
theorem gmpPhysicalC0KernelSemigroup_euclideanNormFourth_local_integrable_le
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ (x : Vec d) (t : ℝ≥0), (t : ℝ) ≤ δ →
      Integrable (fun y => euclideanNorm (y - x) ^ 4)
        (gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x) ∧
      (∫ y, euclideanNorm (y - x) ^ 4 ∂
        (gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x)) ≤ C * (t : ℝ) ^ 2 := by
  have heq (x y : Vec d) : euclideanNorm (y - x) ^ 4 =
      (∑ k : Fin d, (y k - x k) ^ 2) ^ 2 := by
    have hs : euclideanNorm (y - x) ^ 2 = ∑ k : Fin d, (y k - x k) ^ 2 := by
      unfold euclideanNorm euclideanSq dot
      rw [Real.sq_sqrt]
      · simp only [Pi.sub_apply, pow_two]
      · exact Finset.sum_nonneg (fun k _ => mul_self_nonneg _)
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hs]
  obtain ⟨C, δ, hC, hδ, hm⟩ :=
    gmpPhysicalC0KernelSemigroup_euclideanFourth_local_integrable_le hd ω lam Λ hΛ hω hSmooth
  refine ⟨C, δ, hC, hδ, ?_⟩
  intro x t ht
  simpa only [heq] using hm x t ht


/-- A bounded Euclidean displacement moment has a quadratic estimate for every unit time. -/
theorem gmpPhysicalC0KernelSemigroup_boundedEuclideanFourth_le
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : Vec d) (t : ℝ≥0), (t : ℝ) ≤ 1 →
      Integrable (fun y => min (euclideanNorm (y - x) ^ 4) 1)
        (gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x) ∧
      (∫ y, min (euclideanNorm (y - x) ^ 4) 1 ∂
        (gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x)) ≤ C * (t : ℝ) ^ 2 := by
  obtain ⟨C, δ, hC, hδ, hm⟩ :=
    gmpPhysicalC0KernelSemigroup_euclideanNormFourth_local_integrable_le hd ω lam Λ hΛ hω hSmooth
  refine ⟨C + (δ ^ 2)⁻¹, by positivity, ?_⟩
  intro x t _ht
  let P := gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth
  let μ := P t x
  letI : IsProbabilityMeasure μ := ⟨gmpPhysicalC0KernelSemigroup_conservative hd ω lam Λ hΛ hω hSmooth t x⟩
  have hcont : Continuous (fun y : Vec d => min (euclideanNorm (y - x) ^ 4) 1) := by
    have he : Continuous (fun y : Vec d => euclideanNorm (y - x)) := by
      unfold euclideanNorm euclideanSq dot
      fun_prop
    exact (he.pow 4).min continuous_const
  have h0 (y : Vec d) : 0 ≤ min (euclideanNorm (y - x) ^ 4) 1 :=
    le_min (by positivity) (by norm_num)
  have hbound (y : Vec d) : min (euclideanNorm (y - x) ^ 4) 1 ≤ 1 := min_le_right _ _
  have hi : Integrable (fun y => min (euclideanNorm (y - x) ^ 4) 1) μ :=
    (integrable_const (1 : ℝ)).mono_nonneg hcont.aestronglyMeasurable
      (ae_of_all _ h0) (ae_of_all _ hbound)
  refine ⟨hi, ?_⟩
  by_cases hsmall : (t : ℝ) ≤ δ
  · have h := integral_mono hi (hm x t hsmall).1 (fun y => min_le_left _ _)
    have hh := (hm x t hsmall).2
    have hpos : 0 ≤ (δ ^ 2)⁻¹ * (t : ℝ) ^ 2 := by positivity
    nlinarith
  · have hb := integral_mono hi (integrable_const (1 : ℝ)) hbound
    simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at hb
    have hδt : δ ≤ (t : ℝ) := le_of_not_ge hsmall
    have hs : δ ^ 2 ≤ (t : ℝ) ^ 2 := by nlinarith [t.coe_nonneg]
    have hδsq : 0 < δ ^ 2 := by positivity
    have hinv : 1 ≤ (δ ^ 2)⁻¹ * (t : ℝ) ^ 2 := by
      rw [inv_mul_eq_div, one_le_div hδsq]
      exact hs
    have hp : 0 ≤ C * (t : ℝ) ^ 2 := by positivity
    nlinarith


/-- Extended nonnegative form of the bounded fourth-moment estimate. -/
theorem gmpPhysicalC0KernelSemigroup_boundedEuclideanFourth_lintegral_le
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : Vec d) (t : ℝ≥0), (t : ℝ) ≤ 1 →
      (∫⁻ y, ENNReal.ofReal (min (euclideanNorm (y - x) ^ 4) 1) ∂
        (gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth t x)) ≤
          ENNReal.ofReal (C * (t : ℝ) ^ 2) := by
  obtain ⟨C, hC, hm⟩ :=
    gmpPhysicalC0KernelSemigroup_boundedEuclideanFourth_le hd ω lam Λ hΛ hω hSmooth
  refine ⟨C, hC, ?_⟩
  intro x t ht
  rw [← ofReal_integral_eq_lintegral_ofReal (hm x t ht).1
    (ae_of_all _ (fun y => le_min (by positivity) (by norm_num)))]
  exact ENNReal.ofReal_le_ofReal (hm x t ht).2

section PhysicalExhaustion

/-- The norm-induced metric on the coordinate space. -/
local instance instMetricSpaceVec (d : ℕ) : MetricSpace (Vec d) :=
  (inferInstance : NormedAddCommGroup (Vec d)).toMetricSpace

/-- The norm-induced extended metric on the coordinate space. -/
local instance instPseudoEMetricSpaceVec (d : ℕ) : PseudoEMetricSpace (Vec d) :=
  (inferInstance : NormedAddCommGroup (Vec d)).toMetricSpace.toPseudoMetricSpace.toPseudoEMetricSpace

/-- A bounded positive exhaustion of the physical coordinate space. -/
def gmpPhysicalExhaustion {d : ℕ} (x : Vec d) : ℝ :=
  MarkovProcess.heatExhaustion ‖x‖

theorem gmpPhysicalExhaustion_lipschitz {d : ℕ} :
    LipschitzWith 1 (gmpPhysicalExhaustion : Vec d → ℝ) := by
  have hn : LipschitzWith 1 (norm : Vec d → ℝ) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one, one_mul, Real.dist_eq]
    exact abs_norm_sub_norm_le x y
  unfold gmpPhysicalExhaustion
  simpa only [one_mul, Function.comp_def] using
    MarkovProcess.lipschitzWith_one_heatExhaustion.comp hn

theorem gmpPhysicalExhaustion_continuous {d : ℕ} :
    Continuous (gmpPhysicalExhaustion : Vec d → ℝ) :=
  gmpPhysicalExhaustion_lipschitz.continuous

theorem gmpPhysicalExhaustion_pos {d : ℕ} (x : Vec d) :
    0 < gmpPhysicalExhaustion x := MarkovProcess.heatExhaustion_pos ‖x‖

theorem gmpPhysicalExhaustion_le_one {d : ℕ} (x : Vec d) :
    gmpPhysicalExhaustion x ≤ 1 := MarkovProcess.heatExhaustion_le_one ‖x‖

theorem gmpPhysicalExhaustion_superlevel_compact {d : ℕ} (ε : ℝ) (hε : 0 < ε) :
    IsCompact {x : Vec d | ε ≤ gmpPhysicalExhaustion x} := by
  apply IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Vec d) ε⁻¹)
    (isClosed_le continuous_const gmpPhysicalExhaustion_continuous)
  intro x hx
  have hmul : ε * (1 + ‖x‖) ≤ 1 := by
    change ε ≤ 1 / (1 + |‖x‖|) at hx
    rw [abs_of_nonneg (norm_nonneg x)] at hx
    exact (le_div_iff₀ (by positivity : 0 < 1 + ‖x‖)).mp hx
  have hn : ‖x‖ ≤ ε⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ hε]
    calc
      ‖x‖ * ε ≤ (1 + ‖x‖) * ε :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hε.le
      _ = ε * (1 + ‖x‖) := mul_comm _ _
      _ ≤ 1 := hmul
  simpa only [Metric.mem_closedBall, dist_zero_right] using hn

/-- The compactification metric has diameter at most two. -/
theorem gmpPhysicalExhaustion_dist_le_two {d : ℕ} (z w : OnePoint (Vec d)) :
    letI := OnePoint.exhaustionMetricSpace (gmpPhysicalExhaustion (d := d))
      gmpPhysicalExhaustion_continuous gmpPhysicalExhaustion_pos
      gmpPhysicalExhaustion_lipschitz gmpPhysicalExhaustion_superlevel_compact
    dist z w ≤ 2 := by
  let := OnePoint.exhaustionMetricSpace (gmpPhysicalExhaustion (d := d))
    gmpPhysicalExhaustion_continuous gmpPhysicalExhaustion_pos
    gmpPhysicalExhaustion_lipschitz gmpPhysicalExhaustion_superlevel_compact
  induction z using OnePoint.rec with
  | infty =>
      induction w using OnePoint.rec with
      | infty => simp
      | coe y =>
          have h : dist (OnePoint.infty : OnePoint (Vec d)) (y : OnePoint (Vec d)) =
              gmpPhysicalExhaustion y := by rw [dist_comm]; rfl
          rw [h]
          linarith [gmpPhysicalExhaustion_le_one y]
  | coe x =>
      induction w using OnePoint.rec with
      | infty =>
          change gmpPhysicalExhaustion x ≤ 2
          linarith [gmpPhysicalExhaustion_le_one x]
      | coe y =>
          change min (dist x y) (gmpPhysicalExhaustion x + gmpPhysicalExhaustion y) ≤ 2
          exact (min_le_right _ _).trans (by
            linarith [gmpPhysicalExhaustion_le_one x, gmpPhysicalExhaustion_le_one y])

/-- Compactified live-point fourth powers are controlled by bounded physical displacements. -/
theorem gmpPhysicalExhaustion_live_dist_fourth_le {d : ℕ} (x y : Vec d) :
    letI := OnePoint.exhaustionMetricSpace (gmpPhysicalExhaustion (d := d))
      gmpPhysicalExhaustion_continuous gmpPhysicalExhaustion_pos
      gmpPhysicalExhaustion_lipschitz gmpPhysicalExhaustion_superlevel_compact
    dist (y : OnePoint (Vec d)) (x : OnePoint (Vec d)) ^ 4 ≤
      16 * min (‖y - x‖ ^ 4) 1 := by
  let := OnePoint.exhaustionMetricSpace (gmpPhysicalExhaustion (d := d))
    gmpPhysicalExhaustion_continuous gmpPhysicalExhaustion_pos
    gmpPhysicalExhaustion_lipschitz gmpPhysicalExhaustion_superlevel_compact
  have hdist : dist (y : OnePoint (Vec d)) (x : OnePoint (Vec d)) ≤ ‖y - x‖ := by
    calc
      dist (y : OnePoint (Vec d)) (x : OnePoint (Vec d)) ≤ dist y x :=
        OnePoint.exhaustionMetricSpace_dist_coe_coe_le gmpPhysicalExhaustion
          gmpPhysicalExhaustion_continuous gmpPhysicalExhaustion_pos
          gmpPhysicalExhaustion_lipschitz gmpPhysicalExhaustion_superlevel_compact y x
      _ = ‖y - x‖ := dist_eq_norm _ _
  have htwo := gmpPhysicalExhaustion_dist_le_two (y : OnePoint (Vec d)) (x : OnePoint (Vec d))
  have hpow : dist (y : OnePoint (Vec d)) (x : OnePoint (Vec d)) ^ 4 ≤ ‖y - x‖ ^ 4 :=
    pow_le_pow_left₀ dist_nonneg hdist 4
  have hpow2 : dist (y : OnePoint (Vec d)) (x : OnePoint (Vec d)) ^ 4 ≤ (2 : ℝ) ^ 4 :=
    pow_le_pow_left₀ dist_nonneg htwo 4
  by_cases h : ‖y - x‖ ^ 4 ≤ 1
  · rw [min_eq_left h]
    nlinarith [sq_nonneg (‖y - x‖ ^ 2)]
  · rw [min_eq_right (le_of_not_ge h)]
    norm_num at hpow2 ⊢
    exact hpow2

/-- The compactification metric is controlled by the explicit Euclidean displacement. -/
theorem gmpPhysicalExhaustion_live_euclidean_fourth_le {d : ℕ} (x y : Vec d) :
    letI := OnePoint.exhaustionMetricSpace (gmpPhysicalExhaustion (d := d))
      gmpPhysicalExhaustion_continuous gmpPhysicalExhaustion_pos
      gmpPhysicalExhaustion_lipschitz gmpPhysicalExhaustion_superlevel_compact
    dist (y : OnePoint (Vec d)) (x : OnePoint (Vec d)) ^ 4 ≤
      16 * min (euclideanNorm (y - x) ^ 4) 1 := by
  let := OnePoint.exhaustionMetricSpace (gmpPhysicalExhaustion (d := d))
    gmpPhysicalExhaustion_continuous gmpPhysicalExhaustion_pos
    gmpPhysicalExhaustion_lipschitz gmpPhysicalExhaustion_superlevel_compact
  have hn : ‖y - x‖ ≤ euclideanNorm (y - x) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
    intro i
    rw [Real.norm_eq_abs]
    unfold euclideanSq dot
    apply Real.abs_le_sqrt
    rw [sq]
    exact Finset.single_le_sum (f := fun j => (y - x) j * (y - x) j)
      (fun j _ => mul_self_nonneg _) (Finset.mem_univ i)
  calc
    dist (y : OnePoint (Vec d)) (x : OnePoint (Vec d)) ^ 4 ≤
        16 * min (‖y - x‖ ^ 4) 1 := gmpPhysicalExhaustion_live_dist_fourth_le x y
    _ ≤ 16 * min (euclideanNorm (y - x) ^ 4) 1 := by
      gcongr

/-- The actual compactified physical positive C₀ resolvent semigroup has local fourth-moment
Kolmogorov bounds in the exhaustion metric. -/
theorem gmpPhysicalPositiveC0Resolvent_onePoint_localKolmogorov
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) :
    letI := OnePoint.exhaustionMetricSpace (gmpPhysicalExhaustion (d := d))
      gmpPhysicalExhaustion_continuous gmpPhysicalExhaustion_pos
      gmpPhysicalExhaustion_lipschitz gmpPhysicalExhaustion_superlevel_compact
    ∃ M : ℝ≥0,
      ((gmpPhysicalPositiveC0Resolvent hd ω lam Λ hΛ hω hSmooth).onePointKernelSemigroup).HasLocalKolmogorovMoments 4 2 M 16 := by
  let := OnePoint.exhaustionMetricSpace (gmpPhysicalExhaustion (d := d))
    gmpPhysicalExhaustion_continuous gmpPhysicalExhaustion_pos
    gmpPhysicalExhaustion_lipschitz gmpPhysicalExhaustion_superlevel_compact
  obtain ⟨C, hC, hm⟩ :=
    gmpPhysicalC0KernelSemigroup_boundedEuclideanFourth_lintegral_le hd ω lam Λ hΛ hω hSmooth
  refine ⟨Real.toNNReal (16 * C), by norm_num, by norm_num, ?_, ?_⟩
  · intro h hh z
    have hh' : (h : ℝ) ≤ 1 := by exact_mod_cast hh
    have hrhs : ((Real.toNNReal (16 * C) : ℝ≥0) : ℝ≥0∞) * (h : ℝ≥0∞) ^ (2 : ℝ) =
        16 * ENNReal.ofReal (C * (h : ℝ) ^ 2) := by
      rw [ENNReal.rpow_two, ENNReal.ofReal_mul hC, ENNReal.ofReal_pow h.coe_nonneg,
        ENNReal.ofReal_coe_nnreal, ← mul_assoc]
      congr 1
      rw [show ((Real.toNNReal (16 * C) : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (16 * C) from rfl,
        ENNReal.ofReal_mul (by norm_num)]
      norm_num
    rw [hrhs]
    induction z using OnePoint.rec with
    | infty =>
        rw [(gmpPhysicalPositiveC0Resolvent hd ω lam Λ hΛ hω hSmooth).onePointKernelSemigroup_absorbing,
          lintegral_dirac]
        simp
    | coe x =>
        have hlaw : (gmpPhysicalPositiveC0Resolvent hd ω lam Λ hΛ hω hSmooth).onePointKernelSemigroup h
            (x : OnePoint (Vec d)) =
            (gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth h x).map
              ((↑) : Vec d → OnePoint (Vec d)) := by
          rw [(gmpPhysicalPositiveC0Resolvent hd ω lam Λ hΛ hω hSmooth).onePointKernelSemigroup_apply_coe h x]
          change _ + (1 - (gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth h x) Set.univ) • _ = _
          rw [gmpPhysicalC0KernelSemigroup_conservative hd ω lam Λ hΛ hω hSmooth h x, tsub_self,
            zero_smul, add_zero]
          rfl
        have hmeas : Measurable fun z : OnePoint (Vec d) => edist z (x : OnePoint (Vec d)) ^ (4 : ℝ) :=
          (measurable_edist_left (x := (x : OnePoint (Vec d)))).pow_const 4
        rw [hlaw, lintegral_map hmeas OnePoint.continuous_coe.measurable]
        calc
          (∫⁻ y, edist (y : OnePoint (Vec d)) (x : OnePoint (Vec d)) ^ (4 : ℝ) ∂
              (gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth h x)) ≤
              ∫⁻ y, 16 * ENNReal.ofReal (min (euclideanNorm (y - x) ^ 4) 1) ∂
                (gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth h x) := by
            refine lintegral_mono fun y => ?_
            have hb := gmpPhysicalExhaustion_live_euclidean_fourth_le x y
            rw [edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg (by norm_num),
              show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
            calc
              ENNReal.ofReal (dist (y : OnePoint (Vec d)) (x : OnePoint (Vec d)) ^ 4) ≤
                  ENNReal.ofReal (16 * min (euclideanNorm (y - x) ^ 4) 1) :=
                ENNReal.ofReal_le_ofReal hb
              _ = 16 * ENNReal.ofReal (min (euclideanNorm (y - x) ^ 4) 1) := by
                rw [ENNReal.ofReal_mul (by norm_num)]
                norm_num
          _ = 16 * ∫⁻ y, ENNReal.ofReal (min (euclideanNorm (y - x) ^ 4) 1) ∂
                (gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth h x) :=
            lintegral_const_mul' _ _ (by norm_num)
          _ ≤ 16 * ENNReal.ofReal (C * (h : ℝ) ^ 2) := by
            gcongr
            exact hm x h hh'
  · intro y z
    have hdist : edist z y ≤ 2 := by
      rw [edist_dist]
      calc ENNReal.ofReal (dist z y) ≤ ENNReal.ofReal 2 :=
            ENNReal.ofReal_le_ofReal (gmpPhysicalExhaustion_dist_le_two z y)
        _ = 2 := by
            rw [show (2 : ℝ) = ((2 : ℝ≥0) : ℝ) by norm_num, ENNReal.ofReal_coe_nnreal]
            rfl
    calc edist z y ^ (4 : ℝ) ≤ (2 : ℝ≥0∞) ^ (4 : ℝ) :=
          ENNReal.rpow_le_rpow hdist (by norm_num)
      _ = 16 := by
          rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
          norm_num
      _ = ((16 : ℝ≥0) : ℝ≥0∞) := by norm_num

end PhysicalExhaustion

section GMPLivePath

open MarkovProcess MarkovProcess.SubMarkovKernelSemigroup
open ProbabilityTheory

/-- Apply a state map coordinatewise. -/
def gmpCoordMap {ι α β : Type*} (e : α → β) (path : ι → α) : ι → β := fun i => e (path i)

/-- Coordinatewise application of a measurable state map is measurable. -/
theorem measurable_gmpCoordMap {ι α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {e : α → β} (he : Measurable e) : Measurable (gmpCoordMap e : (ι → α) → ι → β) :=
  measurable_pi_iff.mpr fun i => he.comp (measurable_pi_apply i)

/-- Prepending a state commutes with coordinatewise application of a state map. -/
theorem gmpCoordMap_finCons {n : ℕ} {α β : Type*} (e : α → β) (z : α × (Fin n → α)) :
    gmpCoordMap e (@Fin.cons n (fun _ : Fin (n + 1) => α) z.1 z.2) =
      @Fin.cons n (fun _ : Fin (n + 1) => β) (e z.1) (gmpCoordMap e z.2) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- The finite-time kernels of a semigroup are carried along a measurable state map that
intertwines the one-step kernels. -/
theorem gmpFiniteTimeKernel_apply_embed {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (P : SubMarkovKernelSemigroup α) (P' : SubMarkovKernelSemigroup β)
    (hP : P.IsConservative) (hP' : P'.IsConservative) {e : α → β} (he : Measurable e)
    (hrel : ∀ t x, P' t (e x) = (P t x).map e) :
    ∀ {n : ℕ} (times : FiniteOrderedTimes n) (x : α),
      finiteTimeKernel P' times (e x) =
        (finiteTimeKernel P times x).map (gmpCoordMap e) := by
  intro n
  induction n with
  | zero =>
      intro times x
      simp only [finiteTimeKernel_zero, Kernel.const_apply]
      rw [Measure.map_dirac' (measurable_gmpCoordMap (ι := Fin 0) he)]
      congr 1
      exact Subsingleton.elim _ _
  | succ n ih =>
      intro times x
      let : IsFiniteKernel (P (times 0)) := (P.isSubMarkovKernel (times 0)).isFiniteKernel
      let : IsFiniteKernel (P' (times 0)) := (P'.isSubMarkovKernel (times 0)).isFiniteKernel
      let : IsMarkovKernel (finiteTimeKernel P times.relativeTail) :=
        hP.isMarkovKernel_finiteTimeKernel P _
      let : IsMarkovKernel (finiteTimeKernel P' times.relativeTail) :=
        hP'.isMarkovKernel_finiteTimeKernel P' _
      have hmapn : Measurable
          (gmpCoordMap e : (Fin n → α) → Fin n → β) :=
        measurable_gmpCoordMap he
      have hpair : Measurable (fun z : α × (Fin n → α) ↦
          (e z.1, gmpCoordMap e z.2)) :=
        (he.comp measurable_fst).prodMk (hmapn.comp measurable_snd)
      have hkey : ((P' (times 0)) ⊗ₖ Kernel.prodMkLeft β (finiteTimeKernel P' times.relativeTail))
            (e x) =
          (((P (times 0)) ⊗ₖ Kernel.prodMkLeft α (finiteTimeKernel P times.relativeTail)) x).map
            (fun z : α × (Fin n → α) ↦ (e z.1, gmpCoordMap e z.2)) := by
        ext s hs
        rw [Kernel.compProd_apply hs, Measure.map_apply hpair hs,
          Kernel.compProd_apply (hs.preimage hpair), hrel]
        simp only [Kernel.prodMkLeft_apply]
        rw [lintegral_map (f := fun b => finiteTimeKernel P' times.relativeTail b
          (Prod.mk b ⁻¹' s)) (Kernel.measurable_kernel_prodMk_left hs) he]
        refine lintegral_congr fun a => ?_
        rw [ih times.relativeTail a, Measure.map_apply hmapn (measurable_prodMk_left hs)]
        rfl
      rw [finiteTimeKernel_succ, finiteTimeKernel_succ, Kernel.mapOfMeasurable_eq_map,
        Kernel.mapOfMeasurable_eq_map, Kernel.map_apply _ measurable_finCons,
        Kernel.map_apply _ measurable_finCons, hkey, Measure.map_map measurable_finCons hpair,
        Measure.map_map (measurable_gmpCoordMap he) measurable_finCons]
      congr 1
      funext z
      exact (gmpCoordMap_finCons e z).symm

/-- The finite-set kernels of a semigroup are carried along a measurable state map that
intertwines the one-step kernels. -/
theorem gmpFiniteSetKernel_apply_embed {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (P : SubMarkovKernelSemigroup α) (P' : SubMarkovKernelSemigroup β)
    (hP : P.IsConservative) (hP' : P'.IsConservative) {e : α → β} (he : Measurable e)
    (hrel : ∀ t x, P' t (e x) = (P t x).map e) (I : Finset NNReal) (x : α) :
    finiteSetKernel P' I (e x) =
      (finiteSetKernel P I x).map (gmpCoordMap e) := by
  rw [finiteSetKernel_eq_map, finiteSetKernel_eq_map, Kernel.map_apply _ (measurable_orderedPathToFiniteSet I),
    Kernel.map_apply _ (measurable_orderedPathToFiniteSet I),
    gmpFiniteTimeKernel_apply_embed P P' hP hP' he hrel, Measure.map_map (measurable_orderedPathToFiniteSet I)
      (measurable_gmpCoordMap he),
    Measure.map_map (measurable_gmpCoordMap he) (measurable_orderedPathToFiniteSet I)]
  rfl

/-- Compose a continuous path with a continuous map of the state space. -/
def gmpPathPostcomp {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (e : X → Y) (he : Continuous e) (η : ContinuousPath X) :
    ContinuousPath Y :=
  (ContinuousMap.mk e he).comp η

/-- Postcomposition of paths with an injective map is injective. -/
theorem gmpPathPostcomp_injective {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {e : X → Y} (he : Continuous e)
    (hinj : Function.Injective e) : Function.Injective (gmpPathPostcomp e he) := by
  intro η ζ h
  ext t
  exact hinj (congrArg (fun ω : ContinuousPath Y => ω t) h)

/-- Postcomposition of paths with a continuous injective map is a measurable embedding. -/
theorem measurableEmbedding_gmpPathPostcomp {X Y : Type*} [MetricSpace X] [CompleteSpace X] [SecondCountableTopology X]
    [MetricSpace Y] {e : X → Y} (he : Continuous e)
    (hinj : Function.Injective e) : MeasurableEmbedding (gmpPathPostcomp e he) :=
  (ContinuousMap.continuous_postcomp _).measurableEmbedding (gmpPathPostcomp_injective he hinj)

/-- A total left inverse of a measurable embedding of the state space. -/
noncomputable def gmpPointRetraction {X Y : Type*} [Nonempty X] (e : X → Y) : Y → X :=
  Function.extend e id fun _ => Classical.arbitrary X

/-- The point retraction of a measurable embedding is measurable. -/
theorem measurable_gmpPointRetraction {X Y : Type*} [MeasurableSpace X] [Nonempty X] [MeasurableSpace Y] {e : X → Y}
    (he : MeasurableEmbedding e) : Measurable (gmpPointRetraction e) :=
  he.measurable_extend measurable_id measurable_const

/-- The point retraction is a left inverse of an injective map. -/
theorem gmpPointRetraction_apply {X Y : Type*} [Nonempty X] {e : X → Y} (hinj : Function.Injective e) (x : X) :
    gmpPointRetraction e (e x) = x :=
  hinj.extend_apply _ _ _

/-- A total left inverse of `gmpPathPostcomp`. -/
noncomputable def gmpPathRetraction {X Y : Type*} [TopologicalSpace X] [Nonempty X]
    [TopologicalSpace Y] (e : X → Y) (he : Continuous e) :
    ContinuousPath Y → ContinuousPath X :=
  Function.extend (gmpPathPostcomp e he) id fun _ => ContinuousMap.const NNReal (Classical.arbitrary X)

/-- The path retraction is a left inverse of path postcomposition. -/
theorem gmpPathRetraction_pathPostcomp {X Y : Type*} [TopologicalSpace X] [Nonempty X]
    [TopologicalSpace Y] {e : X → Y}
    (he : Continuous e) (hinj : Function.Injective e) (η : ContinuousPath X) :
    gmpPathRetraction e he (gmpPathPostcomp e he η) = η :=
  (gmpPathPostcomp_injective he hinj).extend_apply _ _ _

/-- The path retraction of a continuous injective map is measurable. -/
theorem measurable_gmpPathRetraction {X Y : Type*} [MetricSpace X] [Nonempty X] [CompleteSpace X] [SecondCountableTopology X]
    [MetricSpace Y] {e : X → Y} (he : Continuous e)
    (hinj : Function.Injective e) : Measurable (gmpPathRetraction e he) :=
  (measurableEmbedding_gmpPathPostcomp he hinj).measurable_extend measurable_id measurable_const

/-- A path that stays in the range of an inducing map is recovered from its retraction. -/
theorem gmpPathPostcomp_pathRetraction {X Y : Type*} [TopologicalSpace X] [Nonempty X]
    [TopologicalSpace Y] {e : X → Y}
    (he : Continuous e) (hinj : Function.Injective e) (hemb : Topology.IsInducing e)
    (ω : ContinuousPath Y) (hω : ∀ t, ω t ∈ Set.range e) :
    gmpPathPostcomp e he (gmpPathRetraction e he ω) = ω := by
  have hrange : ω ∈ Set.range (gmpPathPostcomp e he) := by
    choose f hf using hω
    have hcont : Continuous f := by
      have : Continuous (fun t => e (f t)) := by
        simpa [funext hf] using ω.continuous
      exact hemb.continuous_iff.mpr this
    refine ⟨⟨f, hcont⟩, ?_⟩
    ext t
    exact hf t
  obtain ⟨η, rfl⟩ := hrange
  rw [gmpPathRetraction_pathPostcomp he hinj]

/-- Abstract transport of a continuous-path law along an open embedding of the state space: the
unique live-path Markov kernel with the marginals of `P`. -/
theorem gmpExistsUnique_livePath_of_embedding {X Y : Type*} [MetricSpace X] [MeasurableSpace X]
    [BorelSpace X] [CompleteSpace X] [SecondCountableTopology X]
    [Nonempty X] [instY : MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (P : SubMarkovKernelSemigroup X) (P1 : SubMarkovKernelSemigroup Y)
    (hP : P.IsConservative) (hP1 : P1.IsConservative) {e : X → Y}
    (he : Topology.IsOpenEmbedding e)
    (hrel : ∀ (t : ℝ≥0) (x : X), P1 t (e x) = (P t x).map e)
    (Q : Kernel Y (ContinuousPath Y)) [IsMarkovKernel Q]
    (hQmarg : ∀ I : Finset ℝ≥0, Q.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P1 I)
    (hlive : ∀ x : X, ∀ᵐ ω ∂Q (e x), ∀ t, ω t ∈ Set.range e)
    (huniq : ∀ (Q' : Kernel Y (ContinuousPath Y)) [IsFiniteKernel Q'],
      (∀ I : Finset ℝ≥0, Q'.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P1 I) →
        Q' = Q) :
    ∃! K : Kernel X (ContinuousPath X), IsMarkovKernel K ∧
      ∀ I : Finset ℝ≥0, K.map (ContinuousPath.finsetEvaluation I) = finiteSetKernel P I := by
  classical
  have hcoe : Continuous e := he.continuous
  have hinj : Function.Injective e := he.injective
  have hemb : MeasurableEmbedding e := he.measurableEmbedding
  have hr : Measurable (gmpPointRetraction e) := measurable_gmpPointRetraction hemb
  have hg : Measurable (gmpPathRetraction e hcoe) := measurable_gmpPathRetraction hcoe hinj
  have hpp : Measurable (gmpPathPostcomp e hcoe) :=
    (measurableEmbedding_gmpPathPostcomp hcoe hinj).measurable
  have hfe : ∀ I : Finset ℝ≥0, Measurable (ContinuousPath.finsetEvaluation (alpha := X) I) :=
    fun I => ContinuousPath.measurable_finiteEvaluation _
  have hfe_O : ∀ I : Finset ℝ≥0,
      Measurable (ContinuousPath.finsetEvaluation (alpha := Y) I) :=
    fun I => ContinuousPath.measurable_finiteEvaluation _
  have hfsk : ∀ (I : Finset ℝ≥0) (x : X),
      finiteSetKernel P1 I (e x) = (finiteSetKernel P I x).map (gmpCoordMap e) :=
    fun I x => gmpFiniteSetKernel_apply_embed P P1 hP hP1 hemb.measurable hrel I x
  have hcancel : ∀ {I : Finset ℝ≥0} (ν₁ ν₂ : Measure (I → X)),
      ν₁.map (gmpCoordMap e) = ν₂.map (gmpCoordMap e) → ν₁ = ν₂ := by
    intro I ν₁ ν₂ hν
    have hr' : Measurable (gmpCoordMap (gmpPointRetraction e) : (I → Y) → I → X) :=
      measurable_gmpCoordMap hr
    have := congrArg (Measure.map (gmpCoordMap (gmpPointRetraction e))) hν
    rw [Measure.map_map hr' (measurable_gmpCoordMap hemb.measurable),
      Measure.map_map hr' (measurable_gmpCoordMap hemb.measurable)] at this
    have hid : (gmpCoordMap (gmpPointRetraction e) ∘ gmpCoordMap e : (I → X) → I → X) = id := by
      funext p i
      simp [gmpCoordMap, gmpPointRetraction_apply hinj]
    simpa [hid] using this
  let K : Kernel X (ContinuousPath X) := (Q.comap e hemb.measurable).map (gmpPathRetraction e hcoe)
  have hKx : ∀ x, K x = (Q (e x)).map (gmpPathRetraction e hcoe) := by
    intro x
    simp only [K]
    rw [Kernel.map_apply _ hg, Kernel.comap_apply]
  have hKmarg : ∀ I : Finset ℝ≥0, K.map (ContinuousPath.finsetEvaluation I) =
      finiteSetKernel P I := by
    intro I
    refine Kernel.ext fun x => ?_
    rw [Kernel.map_apply _ (hfe I), hKx]
    refine hcancel _ _ ?_
    rw [Measure.map_map (hfe I) hg, Measure.map_map (measurable_gmpCoordMap hemb.measurable)
      ((hfe I).comp hg), ← hfsk, ← hQmarg I, Kernel.map_apply _ (hfe_O I)]
    refine Measure.map_congr ?_
    filter_upwards [hlive x] with ω hω
    have key := gmpPathPostcomp_pathRetraction hcoe hinj he.isInducing ω hω
    calc (gmpCoordMap e ∘ ContinuousPath.finsetEvaluation I ∘ gmpPathRetraction e hcoe) ω
        = ContinuousPath.finsetEvaluation I (gmpPathPostcomp e hcoe (gmpPathRetraction e hcoe ω)) :=
          rfl
      _ = ContinuousPath.finsetEvaluation I ω := by rw [key]
  have : IsMarkovKernel K := by
    simp only [K]
    exact Kernel.IsMarkovKernel.map _ hg
  refine ⟨K, ⟨inferInstance, hKmarg⟩, ?_⟩
  rintro K' ⟨hK'M, hK'marg⟩
  have hs : MeasurableSet (Set.range e) := he.isOpen_range.measurableSet
  let κ : Kernel Y (ContinuousPath Y) :=
    (K'.map (gmpPathPostcomp e hcoe)).comap (gmpPointRetraction e) hr
  let Q' := Kernel.piecewise hs κ Q
  have hQ'x : ∀ x, Q' (e x) = (K' x).map (gmpPathPostcomp e hcoe) := by
    intro x
    simp only [Q', Kernel.piecewise_apply, κ, Set.mem_range_self, ↓reduceIte]
    rw [Kernel.comap_apply, Kernel.map_apply _ hpp,
      gmpPointRetraction_apply hinj]
  have hQ'marg : ∀ I : Finset ℝ≥0, Q'.map (ContinuousPath.finsetEvaluation I) =
      finiteSetKernel P1 I := by
    intro I
    refine Kernel.ext fun z => ?_
    rw [Kernel.map_apply _ (hfe_O I)]
    by_cases hz : z ∈ Set.range e
    · obtain ⟨x, rfl⟩ := hz
      rw [hQ'x, Measure.map_map (hfe_O I) hpp, hfsk, ← hK'marg I, Kernel.map_apply _ (hfe I),
        Measure.map_map (measurable_gmpCoordMap hemb.measurable) (hfe I)]
      rfl
    · simp only [Q', Kernel.piecewise_apply, hz, ↓reduceIte]
      rw [← Kernel.map_apply _ (hfe_O I), hQmarg I]
  have : IsFiniteKernel Q' := by
    simp only [Q']
    infer_instance
  have hQ' : Q' = Q := huniq Q' hQ'marg
  refine Kernel.ext fun x => ?_
  have h1 : (K' x).map (gmpPathPostcomp e hcoe) = Q (e x) := by
    rw [← hQ'x, hQ']
  rw [hKx, ← h1, Measure.map_map hg hpp]
  have hid : (gmpPathRetraction e hcoe ∘ gmpPathPostcomp e hcoe) = id :=
    funext fun η => gmpPathRetraction_pathPostcomp hcoe hinj η
  rw [hid, Measure.map_id]


/-- A conservative positive `C₀` resolvent with regular compactification has a unique Markov kernel
into live continuous paths with the finite-dimensional distributions of its kernel semigroup. -/
theorem gmpExistsUnique_livePath_of_onePointRegular {X : Type*} [MetricSpace X]
    [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] [CompleteSpace X]
    [SecondCountableTopology X] [Nonempty X] {R : MarkovProcess.PositiveC0ContractiveResolvent X}
    (h : R.OnePointRegular) (hcons : R.kernelSemigroup.IsConservative) :
    ∃! K : Kernel X (ContinuousPath X), IsMarkovKernel K ∧
      ∀ I : Finset ℝ≥0, K.map (ContinuousPath.finsetEvaluation I) =
        finiteSetKernel R.kernelSemigroup I := by
  let := h.metricSpace
  let := h.completeSpace
  have hP1 := R.isConservative_onePointKernelSemigroup
  have hrel : ∀ (t : ℝ≥0) (x : X), R.onePointKernelSemigroup t (x : OnePoint X) =
      (R.kernelSemigroup t x).map ((↑) : X → OnePoint X) := by
    intro t x
    rw [R.onePointKernelSemigroup_apply_coe t x]
    rw [hcons t x, tsub_self, zero_smul, add_zero]
  refine gmpExistsUnique_livePath_of_embedding (instY := h.metricSpace) R.kernelSemigroup R.onePointKernelSemigroup hcons hP1
    (e := ((↑) : X → OnePoint X)) OnePoint.isOpenEmbedding_coe hrel
    (IsConservative.continuousProcess R.onePointKernelSemigroup hP1)
    (fun I => (R.isFellerKernelSemigroup_onePointKernelSemigroup
      ).continuousProcess_map_finiteEvaluation R.onePointKernelSemigroup hP1
        h.kolmogorovRegular I)
    (fun x => (h.ae_exitTime_eq_top one_pos x
      (hcons.ofReal_mul_kernelResolvent_one one_pos x)).mono fun ω hω =>
      (ContinuousPath.exitTime_eq_top_iff _ ω).mp hω)
    ?_
  intro Q' _ hQ'
  exact @IsConservative.eq_continuousProcess_of_map_finiteEvaluation (OnePoint X) h.metricSpace
    h.completeSpace OnePoint.instMeasurableSpace _ _ _ R.onePointKernelSemigroup hP1
    h.kolmogorovRegular Q' ‹_› hQ'


/-- The actual compactified physical resolvent satisfies the regularity data of the continuous-path
construction, with the physical exhaustion and the local fourth-moment Kolmogorov bound. -/
noncomputable def gmpPhysicalOnePointRegular {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) :
    (gmpPhysicalPositiveC0Resolvent hd ω lam Λ hΛ hω hSmooth).OnePointRegular where
  rho := gmpPhysicalExhaustion
  continuous_rho := gmpPhysicalExhaustion_continuous
  rho_pos := gmpPhysicalExhaustion_pos
  lipschitz_rho := gmpPhysicalExhaustion_lipschitz
  isCompact_superlevel := gmpPhysicalExhaustion_superlevel_compact
  kolmogorovRegular := by
    let := OnePoint.exhaustionMetricSpace (gmpPhysicalExhaustion (d := d))
      gmpPhysicalExhaustion_continuous gmpPhysicalExhaustion_pos
      gmpPhysicalExhaustion_lipschitz gmpPhysicalExhaustion_superlevel_compact
    let : CompleteSpace (OnePoint (Vec d)) :=
      completeSpace_of_isComplete_univ isCompact_univ.isComplete
    obtain ⟨M, hM⟩ :=
      gmpPhysicalPositiveC0Resolvent_onePoint_localKolmogorov hd ω lam Λ hΛ hω hSmooth
    exact SubMarkovKernelSemigroup.KolmogorovRegular.of_hasKolmogorovMoments _
      (gmpPhysicalPositiveC0Resolvent hd ω lam Λ hΛ hω hSmooth).isConservative_onePointKernelSemigroup
      (hM.toHasKolmogorovMoments
        (gmpPhysicalPositiveC0Resolvent hd ω lam Λ hΛ hω hSmooth).isConservative_onePointKernelSemigroup)

/-- The physical C₀ kernel semigroup has a unique Markov kernel into continuous live paths with its
finite-dimensional distributions. -/
theorem gmpPhysicalC0KernelSemigroup_existsUnique_continuous_realization
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) :
    ∃! K : ProbabilityTheory.Kernel (Vec d) (Path d),
      ProbabilityTheory.IsMarkovKernel K ∧ ∀ I : Finset ℝ≥0,
        K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
          MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
            (gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth) I :=
  gmpExistsUnique_livePath_of_onePointRegular
    (gmpPhysicalOnePointRegular hd ω lam Λ hΛ hω hSmooth)
    (gmpPhysicalC0KernelSemigroup_conservative hd ω lam Λ hΛ hω hSmooth)

end GMPLivePath

end EinsteinFull.Blueprint
