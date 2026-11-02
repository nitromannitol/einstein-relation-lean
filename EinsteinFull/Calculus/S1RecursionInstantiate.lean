import EinsteinFull.Calculus.S1RecursionAssembly

/-! Constructors used when the abstract recursion is applied to the covariance field:
coordinate fields from a vector-valued field, and `L2Vec` structures for the blocks whose
Euclidean size is controlled by the block estimates. -/

open MeasureTheory ProbabilityTheory

namespace EinsteinFull.Calculus.S1
open EinsteinFull EinsteinRelation

variable {d : ℕ}

section

variable {μ : Measure (FieldPair d)} [IsProbabilityMeasure μ] {ι : Type*} [Fintype ι]

omit [IsProbabilityMeasure μ] [Fintype ι] in
theorem lsf_of_vec {V : Vec d → Set (Vec d)} {Fld : Vec d → FieldPair d → ι → ℝ}
    (hmeas : AEStronglyMeasurable (fun p : Vec d × FieldPair d => Fld p.1 p.2)
      (volume.prod μ))
    (hL2 : ∀ x a, MemLp (fun ω => Fld x ω a) 2 μ) (hmean : ∀ x a, ∫ ω, Fld x ω a ∂μ = 0)
    (hloc : ∀ x, ∃ g : FieldPair d → ι → ℝ, Measurable[localSigma (V x)] g ∧ g =ᵐ[μ] Fld x)
    (hstat : ∀ x, Fld x =ᵐ[μ] fun ω => Fld 0 (translate x ω)) :
    ∀ a, LocalStationaryField μ V (fun x ω => Fld x ω a) := by
  intro a
  refine ⟨?_, fun x => hL2 x a, fun x => hmean x a, fun x => ?_, fun x => ?_⟩
  · exact (continuous_apply a).comp_aestronglyMeasurable hmeas
  · obtain ⟨g, hg, hge⟩ := hloc x
    refine ⟨fun ω => g ω a, ?_, hge.mono fun ω hω => congrFun hω a⟩
    exact (measurable_pi_apply a).comp hg
  · exact (hstat x).mono fun ω hω => congrFun hω a

omit [Fintype ι] in
theorem aesm_blk_one {V : Vec d → Set (Vec d)} {F : ι → Vec d → FieldPair d → ℝ}
    (h : ∀ a, LocalStationaryField μ V (F a)) (hT : ∀ x, MeasurePreserving (translate x) μ μ)
    (n : ℝ) {C : Set (Vec d)} (hC : volume C < ⊤) (a : ι) :
    AEStronglyMeasurable (fun ω => blk n F C (fun _ => (1 : ℝ)) ω a) μ := by
  have e : (fun ω => blk n F C (fun _ => (1 : ℝ)) ω a) = fun ω => n * ∫ y in C, F a y ω := by
    funext ω
    simp [blk]
  rw [e]
  exact (((h a).integrable_block hT hC).const_mul n).aestronglyMeasurable

theorem L2Vec_blk_one {V : Vec d → Set (Vec d)} {F : ι → Vec d → FieldPair d → ℝ}
    (h : ∀ a, LocalStationaryField μ V (F a)) (hT : ∀ x, MeasurePreserving (translate x) μ μ)
    (n : ℝ) {C : Set (Vec d)} (hC : volume C < ⊤)
    (hsize : MemLp (fun ω => vsize (blk n F C (fun _ => (1 : ℝ)) ω)) 2 μ) :
    L2Vec μ (blk n F C (fun _ => (1 : ℝ))) :=
  ⟨aesm_blk_one h hT n hC, hsize⟩

theorem L2Vec_strip {V : Vec d → Set (Vec d)} {F : ι → Vec d → FieldPair d → ℝ}
    (h : ∀ a, LocalStationaryField μ V (F a)) (hT : ∀ x, MeasurePreserving (translate x) μ μ)
    (n L w : ℝ) (hw : 0 ≤ w) (x : Vec d)
    (hsize : MemLp (fun ω => vsize (blk n F (clockBlockCube x L) (stripFn x L w) ω)) 2 μ) :
    L2Vec μ (blk n F (clockBlockCube x L) (stripFn x L w)) := by
  refine ⟨fun a => ?_, hsize⟩
  have hae := blk_strip_decomp h hT n L w hw x
  have m1 := aesm_blk_one h hT n (volume_clockBlockCube_lt_top x L) a
  have m2 := aesm_blk_one h hT n (volume_clockBlockCube_lt_top x (L - w)) a
  exact (m1.sub m2).congr (hae.mono fun ω hω => hω a)

theorem L2Vec_diff_blk {V₁ V₂ : Vec d → Set (Vec d)} {F₁ F₂ : ι → Vec d → FieldPair d → ℝ}
    (h1 : ∀ a, LocalStationaryField μ V₁ (F₁ a)) (h2 : ∀ a, LocalStationaryField μ V₂ (F₂ a))
    (hT : ∀ x, MeasurePreserving (translate x) μ μ) (n : ℝ) {C : Set (Vec d)}
    (hC : volume C < ⊤)
    (hsize : MemLp (fun ω => vsize (fun a => blk n F₂ C (fun _ => (1 : ℝ)) ω a -
      blk n F₁ C (fun _ => (1 : ℝ)) ω a)) 2 μ) :
    L2Vec μ (fun ω a => blk n F₂ C (fun _ => (1 : ℝ)) ω a -
      blk n F₁ C (fun _ => (1 : ℝ)) ω a) :=
  ⟨fun a => (aesm_blk_one h2 hT n hC a).sub (aesm_blk_one h1 hT n hC a), hsize⟩

theorem blk_identDistrib {V : Vec d → Set (Vec d)} {F : ι → Vec d → FieldPair d → ℝ}
    (h : ∀ a, LocalStationaryField μ V (F a)) (hT : ∀ x, MeasurePreserving (translate x) μ μ)
    (n : ℝ) (c : Vec d) (L' : ℝ) :
    IdentDistrib (blk n F (clockBlockCube c L') (fun _ => (1 : ℝ)))
      (blk n F (clockBlockCube 0 L') (fun _ => (1 : ℝ))) μ μ := by
  rw [blk_one, blk_one]
  exact blocks_identDistrib h hT n c L'

theorem blk_iIndepFun {V : Vec d → Set (Vec d)} {F : ι → Vec d → FieldPair d → ℝ}
    {r₀ ρ L L' : ℝ} (hfr : HasFiniteRange r₀ μ)
    (hV : ∀ y z, z ∈ V y → euclideanNorm (z - y) < ρ)
    (h : ∀ a, LocalStationaryField μ V (F a))
    (hT : ∀ x, MeasurePreserving (translate x) μ μ) (n : ℝ)
    (hs : r₀ < L - L' - 2 * ρ) :
    iIndepFun (fun (j : Fin d → Fin 2) =>
      blk n F (clockBlockCube (childCenter L j) L') (fun _ => (1 : ℝ))) μ := by
  have e : (fun (j : Fin d → Fin 2) =>
      blk n F (clockBlockCube (childCenter L j) L') (fun _ => (1 : ℝ))) =
      fun j ω a => n * ∫ y in clockBlockCube (childCenter L j) L', F a y ω := by
    funext j
    exact blk_one _ _ _
  rw [e]
  exact blocks_iIndepFun hfr hV h hT n hs

omit [Fintype ι] in
theorem blk_integrable_mean {V : Vec d → Set (Vec d)} {F : ι → Vec d → FieldPair d → ℝ}
    (h : ∀ a, LocalStationaryField μ V (F a)) (hT : ∀ x, MeasurePreserving (translate x) μ μ)
    (n : ℝ) {C : Set (Vec d)} (hC : volume C < ⊤) (a : ι) :
    Integrable (fun ω => blk n F C (fun _ => (1 : ℝ)) ω a) μ ∧
      ∫ ω, blk n F C (fun _ => (1 : ℝ)) ω a ∂μ = 0 := by
  have e : (fun ω => blk n F C (fun _ => (1 : ℝ)) ω a) = fun ω => n * ∫ y in C, F a y ω := by
    funext ω
    simp [blk]
  rw [e]
  refine ⟨((h a).integrable_block hT hC).const_mul n, ?_⟩
  rw [integral_const_mul, (h a).integral_block hT hC, mul_zero]

end

end EinsteinFull.Calculus.S1
