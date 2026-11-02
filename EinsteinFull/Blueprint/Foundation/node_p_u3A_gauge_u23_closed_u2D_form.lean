import EinsteinFull.Proofs.Gauge

open scoped ENNReal
open MeasureTheory

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `p:gauge#closed-form`, `paper/main.tex:605–606`.
The actual exponential multiplication is unitary, both complete H1 graphs
are closed, and transport of their full domains preserves the physical form.
No stationary law or finite-range hypothesis is present. -/
def node_p_u3A_gauge_u23_closed_u2D_formStmt : Prop :=
  ∀ (d : ℕ) (_hd : 2 ≤ d) (i : Fin d) (Λ B : ℝ)
    (hΛ : 1 ≤ Λ) (_hB : 0 ≤ B) (a : Vec d → Mat d)
    (ha : IsElliptic Λ a) (_haLip : IsOperatorLipschitz B a)
    (haSmooth : ∀ j k : Fin d, ContDiff ℝ (⊤ : ℕ∞) (fun x => a x j k))
    (lam s : ℝ) (_hs : 0 ≤ s),
    let hcoef : ∀ (m : Measure (Vec d)) (j k : Fin d),
      MemLp (fun x => (a x j k : ℂ)) ∞ m := fun m j k =>
        memLp_complex_elliptic_entry m a Λ (lt_of_lt_of_le zero_lt_one hΛ) ha
          (fun j k => (haSmooth j k).continuous) j k
    ∃ U : Lp ℂ 2 (physicalForceMeasure i lam) ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure (Vec d)),
    (∀ f : Lp ℂ 2 (physicalForceMeasure i lam),
      (U f : Vec d → ℂ) =ᵐ[volume] physicalGaugeMultiplier i lam f) ∧
    IsClosed {p : Lp ℂ 2 (physicalForceMeasure i lam) ×
      (Fin d → Lp ℂ 2 (physicalForceMeasure i lam)) |
      IsPhysicalH1Graph (physicalForceMeasure i lam) (Or.inr ⟨i, lam, rfl⟩) p.1 p.2} ∧
    IsClosed {p : Lp ℂ 2 (volume : Measure (Vec d)) ×
      (Fin d → Lp ℂ 2 (volume : Measure (Vec d))) |
      IsPhysicalH1Graph volume (Or.inl rfl) p.1 p.2} ∧
    (∀ f : Lp ℂ 2 (physicalForceMeasure i lam),
      (∃ G, IsPhysicalH1Graph (physicalForceMeasure i lam) (Or.inr ⟨i, lam, rfl⟩) f G) ↔
        ∃ H, IsPhysicalH1Graph volume (Or.inl rfl) (U f) H) ∧
    (∀ (f : Lp ℂ 2 (physicalForceMeasure i lam))
      (G : Fin d → Lp ℂ 2 (physicalForceMeasure i lam)),
      IsPhysicalH1Graph (physicalForceMeasure i lam) (Or.inr ⟨i, lam, rfl⟩) f G →
      ∃ H : Fin d → Lp ℂ 2 (volume : Measure (Vec d)),
        IsPhysicalH1Graph volume (Or.inl rfl) (U f) H ∧
        ∀ j : Fin d, (H j : Vec d → ℂ) =ᵐ[volume] fun x =>
          (Real.exp (lam * x i) : ℂ) * (G j x + (lam : ℂ) *
            (unitVector i j : ℂ) * f x)) ∧
    (∀ (f g : Lp ℂ 2 (physicalForceMeasure i lam))
      (G H : Fin d → Lp ℂ 2 (physicalForceMeasure i lam))
      (G' H' : Fin d → Lp ℂ 2 (volume : Measure (Vec d))),
      IsPhysicalH1Graph (physicalForceMeasure i lam) (Or.inr ⟨i, lam, rfl⟩) f G →
      IsPhysicalH1Graph (physicalForceMeasure i lam) (Or.inr ⟨i, lam, rfl⟩) g H →
      IsPhysicalH1Graph volume (Or.inl rfl) (U f) G' → IsPhysicalH1Graph volume (Or.inl rfl) (U g) H' →
      physicalBilinearForm (physicalForceMeasure i lam) a (hcoef _) i s 0
        f (fun j => G j) g (fun j => H j) =
      physicalBilinearForm volume a (hcoef _) i s (lam : ℂ)
        (U f) (fun j => G' j) (U g) (fun j => H' j))

/-- The already proved physical gauge proposition supplies this graph leaf. -/
theorem node_p_u3A_gauge_u23_closed_u2D_form_of_deps : node_p_u3A_gauge_u23_closed_u2D_formStmt := by
  intro d hd i Λ B hΛ hB a ha haLip haSmooth lam s hs
  obtain ⟨U, hU, hcw, hc, hdom, hgrad, hform, _, _⟩ :=
    EinsteinFull.Proofs.gauge d hd i Λ B hΛ hB a ha haLip haSmooth lam s hs
  exact ⟨U, hU, hcw, hc, hdom, hgrad, hform⟩

end EinsteinFull.Blueprint
