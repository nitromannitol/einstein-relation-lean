import EinsteinFull.Frozen.EndpointIndex
import EinsteinFull.Frozen.EndpointDriftSign
import EinsteinRelation.Environment.Basic
import Mathlib.Basic.Complex.Basic

/-!
# Endpoint-index bookkeeping for `e:flux-identity`
-/

namespace EinsteinFull

open EinsteinRelation

/-- The force coefficient of the transpose endpoint's extra term (`2 ζ`), zero otherwise. -/
def fluxIdEps {d : ℕ} (ζ : ℂ) (ν : EndpointIndex d) : ℂ :=
  match ν with
  | .inr true => 2 * ζ
  | _ => 0

/-- The indicator that the endpoint is not the transpose endpoint. -/
def fluxIdKf {d : ℕ} (ν : EndpointIndex d) : ℂ :=
  match ν with
  | .inr true => 0
  | _ => 1

theorem fluxId_cases {d : ℕ} (ζ : ℂ) (ν : EndpointIndex d) :
    (fluxIdEps ζ ν = 0 ∧ fluxIdKf ν = 1 ∧ (endpointDriftSign ν : ℂ) = 1) ∨
    (fluxIdEps ζ ν = 2 * ζ ∧ fluxIdKf ν = 0 ∧ (endpointDriftSign ν : ℂ) = -1) := by
  rcases ν with i0 | b
  · left
    simp [fluxIdEps, fluxIdKf, endpointDriftSign]
  · cases b
    · left
      simp [fluxIdEps, fluxIdKf, endpointDriftSign]
    · right
      simp [fluxIdEps, fluxIdKf, endpointDriftSign]

theorem fluxId_Fmatch {d : ℕ} (ζ : ℂ) (ν : EndpointIndex d) (e u : ℂ) :
    (match ν with
      | .inr true => 2 * ζ * e * u
      | _ => 0) = fluxIdEps ζ ν * e * u := by
  rcases ν with i0 | b
  · simp [fluxIdEps]
  · cases b <;> simp [fluxIdEps]

theorem fluxId_Lmatch {d : ℕ} (ζ : ℂ) (ν : EndpointIndex d) (X : ℂ) :
    (match ν with
      | .inr true => 2 * ζ * X
      | _ => 0) = fluxIdEps ζ ν * X := by
  rcases ν with i0 | b
  · simp [fluxIdEps]
  · cases b <;> simp [fluxIdEps]

theorem fluxId_Dmatch {d : ℕ} (ν : EndpointIndex d) (Y : ℂ) :
    (match ν with
      | .inr true => (0 : ℂ)
      | _ => Y) = fluxIdKf ν * Y := by
  rcases ν with i0 | b
  · simp [fluxIdKf]
  · cases b <;> simp [fluxIdKf]

theorem fluxId_Kmatch {d : ℕ} (ζ : ℂ) (ν : EndpointIndex d) (X : ℂ) :
    (match ν with
      | .inr true => (0 : ℂ)
      | _ => ζ * X) = (fluxIdKf ν * ζ) * X := by
  rcases ν with i0 | b
  · simp [fluxIdKf]
  · cases b <;> simp [fluxIdKf]

end EinsteinFull
