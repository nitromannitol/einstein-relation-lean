import EinsteinRelation.External.AKMHeatKernel
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Haar.Unique

open MeasureTheory
namespace EinsteinRelation.Correctors

/-- Time reflection preserves interval-restricted Lebesgue measure.
Source: `paper/main.tex:787–792,850`. -/
theorem akm_time_reflection_interval_measurePreserving (T a b : ℝ) :
    MeasurePreserving (fun t : ℝ => T-t)
      (volume.restrict (Set.Ioo a b)) (volume.restrict (Set.Ioo (T-b) (T-a))) := by
  let e := MeasurableEquiv.subLeft T
  have ht : MeasurePreserving e volume volume := by
    have hh := (measurePreserving_add_right (volume : Measure ℝ) T).comp
      (Measure.measurePreserving_neg (volume : Measure ℝ))
    convert hh using 1
    ext t
    change T-t = -t+T
    ring
  have hi : e '' Set.Ioo a b = Set.Ioo (T-b) (T-a) := by
    ext t
    constructor
    · rintro ⟨s, hs, rfl⟩
      change T-b < T-s ∧ T-s < T-a
      constructor <;> linarith [hs.1, hs.2]
    · intro ht
      refine ⟨T-t, ?_, ?_⟩
      · constructor <;> linarith [ht.1, ht.2]
      · change T-(T-t) = t
        ring
  simpa only [hi] using ht.restrict_image_emb e.measurableEmbedding (Set.Ioo a b)

/-- Reflection exchanges the positive forward and backward time strips
without changing space-time volume. Source: `paper/main.tex:787–792,850`. -/
theorem akm_time_reflection_cylinder_measurePreserving (d : ℕ) (T a b : ℝ) (U : Set (Vec d)) :
    MeasurePreserving (fun z : ℝ × Vec d => (T-z.1,z.2))
      (volume.restrict (Set.Ioo a b ×ˢ U))
      (volume.restrict (Set.Ioo (T-b) (T-a) ×ˢ U)) := by
  let φ : ℝ × Vec d ≃ᵐ ℝ × Vec d :=
    { toFun := fun z => (T - z.1, z.2)
      invFun := fun z => (T - z.1, z.2)
      left_inv := fun _ => by simp
      right_inv := fun _ => by simp
      measurable_toFun := by
        refine Measurable.prodMk ?_ measurable_snd
        exact measurable_const.sub measurable_fst
      measurable_invFun := by
        refine Measurable.prodMk ?_ measurable_snd
        exact measurable_const.sub measurable_fst
    }
  have h_mp : MeasurePreserving φ volume volume := by
    have h_neg : MeasurePreserving (fun (t : ℝ) => -t) volume volume :=
      Measure.measurePreserving_neg _
    have h_add : MeasurePreserving (fun (t : ℝ) => t + T) volume volume :=
      measurePreserving_add_right volume T
    have h_time : MeasurePreserving (fun (t : ℝ) => T - t) volume volume := by
      have : (fun (t : ℝ) => T - t) = (fun (s : ℝ) => s + T) ∘ (fun (s : ℝ) => -s) := by
        ext t; simp [sub_eq_add_neg, add_comm]
      rw [this]
      exact h_add.comp h_neg
    have h_space : MeasurePreserving (id : Vec d → Vec d) volume volume :=
      MeasurePreserving.id volume
    have h_prod : MeasurePreserving (Prod.map (fun (t : ℝ) => T - t) id) volume volume :=
      MeasurePreserving.prod h_time h_space
    have h_eq : (φ : ℝ × Vec d → ℝ × Vec d) = Prod.map (fun (t : ℝ) => T - t) id := by
      ext ⟨t, x⟩
      dsimp [φ]
      rfl
    rw [h_eq]
    exact h_prod
  have h_emb : MeasurableEmbedding φ :=
    φ.measurableEmbedding
  have h_image : φ '' (Set.Ioo a b ×ˢ U) =
      Set.Ioo (T - b) (T - a) ×ˢ U := by
    ext z
    constructor
    · rintro ⟨⟨t, x⟩, ⟨⟨ht_a, ht_b⟩, hx⟩, rfl⟩
      have h1 : T - b < T - t := by linarith
      have h2 : T - t < T - a := by linarith
      exact ⟨⟨h1, h2⟩, hx⟩
    · rintro ⟨⟨hz_t_l, hz_t_r⟩, hx⟩
      have h1 : a < T - z.1 := by linarith
      have h2 : T - z.1 < b := by linarith
      refine ⟨(T - z.1, z.2), ⟨⟨h1, h2⟩, hx⟩, ?_⟩
      simp [φ]
  have h_result := h_mp.restrict_image_emb h_emb (Set.Ioo a b ×ˢ U)
  rw [h_image] at h_result
  exact h_result


/-- Reflection exchanges the positive forward and backward time strips
without changing space-time volume. Source: `paper/main.tex:787–792,850`. -/
theorem akm_time_reflection_strip_measurePreserving (d : ℕ) (T a b : ℝ) :
    MeasurePreserving (fun z : ℝ × Vec d => (T-z.1,z.2))
      (volume.restrict (Set.Ioo a b ×ˢ (Set.univ : Set (Vec d))))
      (volume.restrict (Set.Ioo (T-b) (T-a) ×ˢ (Set.univ : Set (Vec d)))) := by
  exact akm_time_reflection_cylinder_measurePreserving d T a b Set.univ

end EinsteinRelation.Correctors
