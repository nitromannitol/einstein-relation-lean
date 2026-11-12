import EinsteinRelation.External.AKMCorrectorOscillation

/-! Source: `paper/main.tex:732-748`, AKM (6.7). The heat formula is antisymmetric
in its row and column indices, before any limit is taken. -/
open MeasureTheory Filter Topology
namespace EinsteinRelation.Correctors
open External.AKM HeatSelectedSkewMeaning

/-- The AKM (6.7) density changes sign when its row and column are exchanged. -/
theorem akmHeatGradientDensity_swap {d : ℕ} (g : Vec d → Vec d) (t : ℝ)
    (j k l : Fin d) (x y : Vec d) :
    akmHeatGradientDensity g t k j l x y = -akmHeatGradientDensity g t j k l x y := by
  dsimp [akmHeatGradientDensity]
  by_cases ht : 0 < t
  · simp only [dif_pos ht]
    ring
  · simp only [dif_neg ht, neg_zero]

/-- The spatial heat integral changes sign when row and column are exchanged. -/
theorem akmHeatGradientSpaceIntegral_swap {d : ℕ} (g : Vec d → Vec d) (t : ℝ)
    (j k l : Fin d) (x : Vec d) :
    akmHeatGradientSpaceIntegral g t k j l x = -akmHeatGradientSpaceIntegral g t j k l x := by
  dsimp [akmHeatGradientSpaceIntegral]
  calc
    (∫ y : Vec d, akmHeatGradientDensity g t k j l x y) =
        (∫ y : Vec d, (-akmHeatGradientDensity g t j k l x y)) := by
      refine integral_congr_ae (ae_of_all _ (fun y => ?_))
      simpa using akmHeatGradientDensity_swap g t j k l x y
    _ = -(∫ y : Vec d, akmHeatGradientDensity g t j k l x y) := by rw [integral_neg]

/-- Every literal truncation of AKM (6.7) is antisymmetric in row and column. -/
theorem iteratedAKMHeatGradientTruncation_swap {d : ℕ} (g : Vec d → Vec d) (m n : ℕ)
    (j k l : Fin d) (x : Vec d) :
    iteratedAKMHeatGradientTruncation g m n k j l x =
      -iteratedAKMHeatGradientTruncation g m n j k l x := by
  dsimp [iteratedAKMHeatGradientTruncation]
  have hmeas : MeasurableSet (Set.Icc (((m + 1 : ℕ) : ℝ)⁻¹) ((n + 1 : ℕ) : ℝ)) :=
    measurableSet_Icc
  calc
    (∫ t in Set.Icc (((m + 1 : ℕ) : ℝ)⁻¹) ((n + 1 : ℕ) : ℝ),
        akmHeatGradientSpaceIntegral g t k j l x) =
        (∫ t in Set.Icc (((m + 1 : ℕ) : ℝ)⁻¹) ((n + 1 : ℕ) : ℝ),
          (-akmHeatGradientSpaceIntegral g t j k l x)) := by
      refine setIntegral_congr_fun hmeas ?_
      intro t ht
      simpa using akmHeatGradientSpaceIntegral_swap g t j k l x
    _ = -(∫ t in Set.Icc (((m + 1 : ℕ) : ℝ)⁻¹) ((n + 1 : ℕ) : ℝ),
        akmHeatGradientSpaceIntegral g t j k l x) := by rw [integral_neg]

/-- A heat-selected gradient may be replaced by its row-column antisymmetric
transpose: the same truncations select it. -/
theorem isHeatSelectedFluxGradient_swap {d : ℕ} {g : Vec d → Vec d}
    {G : Fin d → Fin d → Vec d → Vec d} (h : IsHeatSelectedFluxGradient g G) :
    IsHeatSelectedFluxGradient g (fun j k x => -G k j x) := by
  intro j k l R
  have hkj := h k j l R
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- integrability: ∀ m n, ∀ᵐ x, (density int) ∧ (space integral int)
    intro m n
    have hkj_int := hkj.1 m n
    refine hkj_int.mono (fun x hx => ?_)
    rcases hx with ⟨hx_dens, hx_space⟩
    have hx_dens' : ∀ᵐ t ∂(volume.restrict (Set.Icc (((m + 1 : ℕ) : ℝ)⁻¹) ((n + 1 : ℕ) : ℝ))),
        Integrable (fun y : Vec d => akmHeatGradientDensity g t j k l x y) volume := by
      filter_upwards [hx_dens] with t ht
      have h_eq : (fun y : Vec d => akmHeatGradientDensity g t j k l x y) =
          (fun y => -akmHeatGradientDensity g t k j l x y) := by
        ext y
        have h := akmHeatGradientDensity_swap g t k j l x y
        rw [← h]
      rw [h_eq]
      exact ht.neg
    have hx_space' : Integrable (fun (t : ℝ) => akmHeatGradientSpaceIntegral g t j k l x)
        (volume.restrict (Set.Icc (((m + 1 : ℕ) : ℝ)⁻¹) ((n + 1 : ℕ) : ℝ))) := by
      have h_eq : (fun (t : ℝ) => akmHeatGradientSpaceIntegral g t j k l x) =
          (fun t => -akmHeatGradientSpaceIntegral g t k j l x) := by
        ext t
        have h := akmHeatGradientSpaceIntegral_swap g t k j l x
        rw [← h]
      rw [h_eq]
      exact hx_space.neg
    exact ⟨hx_dens', hx_space'⟩
  · -- MemLp of iterated truncation
    intro m n
    have hkj_mem := hkj.2.1 m n
    have h_eq : (fun (x : Vec d) => iteratedAKMHeatGradientTruncation g m n j k l x) =
        (fun x => -iteratedAKMHeatGradientTruncation g m n k j l x) := by
      ext x
      rw [iteratedAKMHeatGradientTruncation_swap g m n k j l x]
    rw [h_eq]
    exact hkj_mem.neg
  · -- MemLp of the gradient
    have hkj_mem_G := hkj.2.2.1
    simpa using hkj_mem_G.neg
  · -- Tendsto condition
    have hTendsto_kj := hkj.2.2.2
    have hTendsto_kj' : Filter.Tendsto (fun (mn : ℕ × ℕ) =>
        eLpNorm (fun x => -iteratedAKMHeatGradientTruncation g mn.1 mn.2 j k l x - G k j x l) 2
          (volume.restrict (ball 0 ((R + 1 : ℕ) : ℝ)))) Filter.atTop (nhds 0) := by
      have h_eq : (fun (mn : ℕ × ℕ) =>
          eLpNorm (fun x => -iteratedAKMHeatGradientTruncation g mn.1 mn.2 j k l x - G k j x l) 2
            (volume.restrict (ball 0 ((R + 1 : ℕ) : ℝ)))) =
          (fun (mn : ℕ × ℕ) =>
            eLpNorm (fun x => iteratedAKMHeatGradientTruncation g mn.1 mn.2 k j l x - G k j x l) 2
              (volume.restrict (ball 0 ((R + 1 : ℕ) : ℝ)))) := by
        funext mn
        simp [iteratedAKMHeatGradientTruncation_swap g mn.1 mn.2 k j l]
      rw [h_eq]
      simpa [Nat.cast_add, Nat.cast_one] using hTendsto_kj
    have hTendsto_sum : Filter.Tendsto (fun (mn : ℕ × ℕ) =>
        eLpNorm (fun x => iteratedAKMHeatGradientTruncation g mn.1 mn.2 j k l x + G k j x l) 2
          (volume.restrict (ball 0 ((R + 1 : ℕ) : ℝ)))) Filter.atTop (nhds 0) := by
      have h_norm_eq : ∀ (mn : ℕ × ℕ),
          eLpNorm (fun x => -iteratedAKMHeatGradientTruncation g mn.1 mn.2 j k l x - G k j x l) 2
            (volume.restrict (ball 0 ((R + 1 : ℕ) : ℝ))) =
          eLpNorm (fun x => iteratedAKMHeatGradientTruncation g mn.1 mn.2 j k l x + G k j x l) 2
            (volume.restrict (ball 0 ((R + 1 : ℕ) : ℝ))) := by
        intro mn
        calc
          eLpNorm (fun x => -iteratedAKMHeatGradientTruncation g mn.1 mn.2 j k l x - G k j x l) 2
              (volume.restrict (ball 0 ((R + 1 : ℕ) : ℝ))) =
            eLpNorm (fun x =>
              -(iteratedAKMHeatGradientTruncation g mn.1 mn.2 j k l x + G k j x l)) 2
              (volume.restrict (ball 0 ((R + 1 : ℕ) : ℝ))) := by
            refine congrArg (fun f => eLpNorm f 2 (volume.restrict (ball 0 ((R + 1 : ℕ) : ℝ)))) ?_
            ext x; ring
          _ = eLpNorm (fun x => iteratedAKMHeatGradientTruncation g mn.1 mn.2 j k l x + G k j x l) 2
              (volume.restrict (ball 0 ((R + 1 : ℕ) : ℝ))) := by
            exact eLpNorm_neg (f := fun x =>
              iteratedAKMHeatGradientTruncation g mn.1 mn.2 j k l x + G k j x l) (p := 2)
              (μ := volume.restrict (ball 0 ((R + 1 : ℕ) : ℝ)))
      have : (fun (mn : ℕ × ℕ) =>
          eLpNorm (fun x => -iteratedAKMHeatGradientTruncation g mn.1 mn.2 j k l x - G k j x l) 2
            (volume.restrict (ball 0 ((R + 1 : ℕ) : ℝ)))) =
          (fun (mn : ℕ × ℕ) =>
            eLpNorm (fun x => iteratedAKMHeatGradientTruncation g mn.1 mn.2 j k l x + G k j x l) 2
              (volume.restrict (ball 0 ((R + 1 : ℕ) : ℝ)))) := by
        ext mn; exact h_norm_eq mn
      rw [this] at hTendsto_kj'
      exact hTendsto_kj'
    simpa [sub_eq_add_neg, neg_neg, Nat.cast_add] using hTendsto_sum

end EinsteinRelation.Correctors
