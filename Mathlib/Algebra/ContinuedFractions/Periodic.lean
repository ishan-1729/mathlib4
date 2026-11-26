/-
Copyright (c) 2026 Ishan Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ishan Singh
-/
module

public import Mathlib.Algebra.ContinuedFractions.Computation.CompleteQuotient

import Mathlib.Algebra.ContinuedFractions.Computation.ApproximationCorollaries
import Mathlib.Algebra.ContinuedFractions.TerminatedStable
import Mathlib.Algebra.Ring.Periodic

/-!
# Periodic continued fractions

We define eventually periodic and purely periodic generalized continued fractions and
characterize, for the continued fraction `GenContFract.of v` of a value `v`, both notions in terms
of the complete quotients of `v`.

## Main definitions

- `GenContFract.IsEventuallyPeriodic`: a continued fraction is eventually periodic if it does not
  terminate and its sequence of partial numerators and denominators is periodic from some index
  on.
- `GenContFract.IsPurelyPeriodic`: a continued fraction `[h; (a₀, b₀), (a₁, b₁), …]` is purely
  periodic if there is `p` such that `bₚ = h` and `(aₙ₊ₚ₊₁, bₙ₊ₚ₊₁) = (aₙ, bₙ)` for all `n`. For a
  regular continued fraction `[c₀; c₁, c₂, …]` this says that `cₙ₊ₚ₊₁ = cₙ` for all `n`.

## Main results

- `GenContFract.of_isEventuallyPeriodic_iff_partDens`: the continued fraction of `v` is eventually
  periodic if and only if it does not terminate and its sequence of partial denominators is
  periodic from some index on.
- `GenContFract.of_isEventuallyPeriodic_iff`: the continued fraction of `v` is eventually periodic
  if and only if it does not terminate and two complete quotients of `v` coincide.
- `GenContFract.of_isPurelyPeriodic_iff`: the continued fraction of `v` is purely periodic if and
  only if it does not terminate and `v` is equal to one of its complete quotients of positive
  index.

## Tags

continued fraction, periodic
-/

@[expose] public section

namespace GenContFract

open GenContFract (of)

section Defs

variable {α : Type*} {g : GenContFract α}

/-- A generalized continued fraction `[h; (a₀, b₀), (a₁, b₁), …]` is *eventually periodic* if it
does not terminate and its sequence of partial numerators and denominators is periodic from some
index on, that is, if there are `N` and `p > 0` such that `(aₙ₊ₚ, bₙ₊ₚ) = (aₙ, bₙ)` for all
`n ≥ N`. Non-termination is part of the definition because the second condition holds for every
terminating continued fraction. -/
def IsEventuallyPeriodic (g : GenContFract α) : Prop :=
  ¬g.Terminates ∧ ∃ N p, 0 < p ∧ ∀ n ≥ N, g.s.get? (n + p) = g.s.get? n

/-- A generalized continued fraction `[h; (a₀, b₀), (a₁, b₁), …]` is *purely periodic* with period
`p + 1` if `bₚ = h` and `(aₙ₊ₚ₊₁, bₙ₊ₚ₊₁) = (aₙ, bₙ)` for all `n`. The period is written as `p + 1`
because the head `h` is the first term of the period, so that `p` is the index of the partial
denominator which repeats `h`.

The head is compared with a partial denominator only. Hence this notion is meant for regular
continued fractions `[c₀; c₁, c₂, …]`, where `c₀ = h`, `cₙ₊₁ = bₙ` and all partial numerators are
`1`: for these it says that `cₙ₊ₚ₊₁ = cₙ` for all `n`.

A purely periodic continued fraction does not terminate, see
`GenContFract.IsPurelyPeriodic.not_terminates`. -/
def IsPurelyPeriodic (g : GenContFract α) : Prop :=
  ∃ p, g.partDens.get? p = some g.h ∧ ∀ n, g.s.get? (n + (p + 1)) = g.s.get? n

/-- An eventually periodic continued fraction does not terminate, by definition. -/
theorem IsEventuallyPeriodic.not_terminates (h : g.IsEventuallyPeriodic) : ¬g.Terminates :=
  h.1

/-- A purely periodic continued fraction does not terminate: the partial denominator `bₚ = h`
appears again at all positions `p + k * (p + 1)`. -/
theorem IsPurelyPeriodic.not_terminates (h : g.IsPurelyPeriodic) : ¬g.Terminates := by
  obtain ⟨p, hp, h⟩ := h
  rintro ⟨n, hn⟩
  have key : g.s.get? (p + n * (p + 1)) = g.s.get? p :=
    Function.Periodic.nat_mul (f := g.s.get?) h n p
  have hn' : g.TerminatedAt (p + n * (p + 1)) :=
    terminated_stable ((Nat.le_mul_of_pos_right n p.succ_pos).trans (Nat.le_add_left ..)) hn
  rw [terminatedAt_iff_s_none, key, ← partDen_none_iff_s_none, hp] at hn'
  exact Option.some_ne_none _ hn'

/-- A purely periodic continued fraction is eventually periodic. -/
theorem IsPurelyPeriodic.isEventuallyPeriodic (h : g.IsPurelyPeriodic) :
    g.IsEventuallyPeriodic :=
  have ⟨p, _, hp⟩ := h
  ⟨h.not_terminates, 0, p + 1, p.succ_pos, fun n _ ↦ hp n⟩

end Defs

/-- The continued fraction of `v` is eventually periodic if and only if it does not terminate and
its sequence of partial denominators is periodic from some index on. -/
theorem of_isEventuallyPeriodic_iff_partDens {K : Type*} [DivisionRing K] [LinearOrder K]
    [FloorRing K] {v : K} :
    (of v).IsEventuallyPeriodic ↔ ¬(of v).Terminates ∧
      ∃ N p, 0 < p ∧ ∀ n ≥ N, (of v).partDens.get? (n + p) = (of v).partDens.get? n := by
  refine and_congr_right fun hv ↦ ?_
  simp [partDens, get?_of_eq_some_of_not_terminatedAt (not_exists.mp hv _)]

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K] {v : K}

/-- The continued fraction of `v` is eventually periodic if and only if it does not terminate and
two complete quotients of `v` coincide. -/
theorem of_isEventuallyPeriodic_iff :
    (of v).IsEventuallyPeriodic ↔ ¬(of v).Terminates ∧
      ∃ N p, 0 < p ∧ completeQuotient v (N + p) = completeQuotient v N := by
  refine and_congr_right fun hv ↦ ⟨fun ⟨N, p, hp, h⟩ ↦ ⟨N + 1, p, hp, of_injective ?_⟩,
    fun ⟨N, p, hp, h⟩ ↦ ⟨N, p, hp, fun n hn ↦ ?_⟩⟩
  · have hN := get?_of_eq_some_of_not_terminatedAt (not_exists.mp hv N)
    have hNp := get?_of_eq_some_of_not_terminatedAt (not_exists.mp hv (N + p))
    rw [h N le_rfl, hN] at hNp
    ext1
    · simpa [add_right_comm N 1 p] using hNp.symm
    · ext1 n
      rw [of_completeQuotient_s_get?, of_completeQuotient_s_get?, add_right_comm (N + 1),
        h _ (by lia)]
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [add_right_comm, ← of_completeQuotient_s_get?, h, of_completeQuotient_s_get?]

/-- The continued fraction of `v` is purely periodic if and only if it does not terminate and `v`
is equal to one of its complete quotients of positive index, that is, `v` is a periodic point of
the map `x ↦ (Int.fract x)⁻¹` (see `Function.periodicPts`). -/
theorem of_isPurelyPeriodic_iff :
    (of v).IsPurelyPeriodic ↔ ¬(of v).Terminates ∧ ∃ p, 0 < p ∧ completeQuotient v p = v := by
  refine ⟨fun h ↦ ⟨h.not_terminates, ?_⟩, fun ⟨hv, p, hp, h⟩ ↦ ?_⟩
  · have hv := h.not_terminates
    obtain ⟨p, hp, hs⟩ := h
    have hvp := get?_of_eq_some_of_not_terminatedAt (not_exists.mp hv p)
    refine ⟨p + 1, p.succ_pos, of_injective ?_⟩
    ext1
    · simpa [partDens, hvp] using hp
    · ext1 n
      rw [of_completeQuotient_s_get?, add_comm, hs]
  · obtain ⟨p, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hp.ne'
    refine ⟨p, ?_, fun n ↦ ?_⟩
    · simp [partDens, get?_of_eq_some_of_not_terminatedAt (not_exists.mp hv p), h]
    · rw [add_comm, ← of_completeQuotient_s_get?, h]

end GenContFract
