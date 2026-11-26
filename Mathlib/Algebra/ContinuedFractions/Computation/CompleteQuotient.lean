/-
Copyright (c) 2026 Ishan Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ishan Singh
-/
module

public import Mathlib.Algebra.ContinuedFractions.Computation.Translations

import Mathlib.Algebra.ContinuedFractions.Computation.Approximations

/-!
# Complete quotients of a continued fraction expansion

Let `v` be an element of a linear ordered field with a floor function. The computation of the
continued fraction `GenContFract.of v` of `v` replaces `v` by `(Int.fract v)⁻¹` at each step. We
call the values `v₀ = v`, `vₙ₊₁ = (Int.fract vₙ)⁻¹` obtained in this way the *complete quotients*
of `v`, so that `v = ⌊v₀⌋ + 1 / (⌊v₁⌋ + 1 / (⌊v₂⌋ + … + 1 / vₙ))`.

In contrast to `GenContFract.IntFractPair.stream`, which stores the pairs `⟨⌊vₙ⌋, Int.fract vₙ⟩`
as long as the computation has not terminated, the complete quotients form a total sequence: once
some `vₙ` is an integer, all later complete quotients are `0`.

The sequence of the complete quotients of `v` is the orbit of `v` under the map
`x ↦ (Int.fract x)⁻¹`. In particular `v` is equal to its `p`-th complete quotient if and only if
`Function.IsPeriodicPt (fun x ↦ (Int.fract x)⁻¹) p v`, by definition.

## Main definitions

- `GenContFract.completeQuotient v n`: the `n`-th complete quotient `vₙ` of `v`.

## Main results

- `GenContFract.of_completeQuotient_s`: the continued fraction of `vₙ` is the `n`-th tail of the
  continued fraction of `v`.
- `GenContFract.of_terminatedAt_iff_fract_completeQuotient_eq_zero`: the continued fraction of `v`
  terminates at position `n` if and only if `vₙ` is an integer.
- `GenContFract.get?_of_eq_some_of_not_terminatedAt`: the `n`-th partial denominator of the
  continued fraction of `v` is `⌊vₙ₊₁⌋`.
- `GenContFract.eq_completeQuotient_mul_contsAux_div`: the formula
  `v = (vₙ₊₁ * Aₙ + Aₙ₋₁) / (vₙ₊₁ * Bₙ + Bₙ₋₁)`, where `Aₙ / Bₙ` are the convergents of `v`.

## References

- [G. H. Hardy and E. M. Wright, *An Introduction to the Theory of Numbers*, Chapter X]
  [hardy2008introduction]

## Tags

continued fraction, complete quotient
-/

@[expose] public section

namespace GenContFract

open GenContFract (of)
open Int

section DivisionRing

variable {K : Type*} [DivisionRing K] [LinearOrder K] [FloorRing K] {v : K} {m n : ℕ}

/-- The `n`-th complete quotient `vₙ` of the continued fraction expansion of `v`, defined by
`v₀ = v` and `vₙ₊₁ = (Int.fract vₙ)⁻¹`. If `vₙ` is an integer, that is if the continued fraction
of `v` terminates at position `n`, then `vₘ = 0` for all `m > n`. -/
def completeQuotient (v : K) (n : ℕ) : K :=
  (fun x ↦ (fract x)⁻¹)^[n] v

@[simp]
theorem completeQuotient_zero (v : K) : completeQuotient v 0 = v :=
  rfl

/-- The recurrence relation `vₙ₊₁ = (Int.fract vₙ)⁻¹` for the complete quotients of `v`. -/
theorem completeQuotient_succ (v : K) (n : ℕ) :
    completeQuotient v (n + 1) = (fract (completeQuotient v n))⁻¹ :=
  Function.iterate_succ_apply' ..

/-- The recurrence relation for the complete quotients of `v` in terms of those of the inverse of
the fractional part of `v`. -/
theorem completeQuotient_succ' (v : K) (n : ℕ) :
    completeQuotient v (n + 1) = completeQuotient (fract v)⁻¹ n :=
  rfl

/-- The `m`-th complete quotient of the `n`-th complete quotient of `v` is the `m + n`-th complete
quotient of `v`. This is `Function.iterate_add_apply` for the map `x ↦ (Int.fract x)⁻¹`. -/
theorem completeQuotient_add (v : K) (m n : ℕ) :
    completeQuotient v (m + n) = completeQuotient (completeQuotient v n) m :=
  Function.iterate_add_apply ..

/-- The `n`-th complete quotient of `v` in terms of the next one: `vₙ = ⌊vₙ⌋ + 1 / vₙ₊₁`. -/
theorem floor_add_inv_completeQuotient_succ (v : K) (n : ℕ) :
    ⌊completeQuotient v n⌋ + (completeQuotient v (n + 1))⁻¹ = completeQuotient v n := by
  rw [completeQuotient_succ, inv_inv, floor_add_fract]

/-- The coefficient sequence of the continued fraction of the `n`-th complete quotient of `v` is
the `n`-th tail of the coefficient sequence of the continued fraction of `v`. -/
theorem of_completeQuotient_s (v : K) (n : ℕ) :
    (of (completeQuotient v n)).s = (of v).s.drop n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => rw [completeQuotient_succ', ih, ← of_s_tail, Stream'.Seq.dropn_tail]

/-- The `n`-th coefficient of the continued fraction of the `m`-th complete quotient of `v` is the
`m + n`-th coefficient of the continued fraction of `v`. -/
theorem of_completeQuotient_s_get? (v : K) (m n : ℕ) :
    (of (completeQuotient v m)).s.get? n = (of v).s.get? (m + n) := by
  rw [of_completeQuotient_s, Stream'.Seq.drop_get?]

/-- The continued fraction of the `m`-th complete quotient of `v` terminates at position `n` if and
only if the continued fraction of `v` terminates at position `m + n`. -/
theorem of_completeQuotient_terminatedAt_iff :
    (of (completeQuotient v m)).TerminatedAt n ↔ (of v).TerminatedAt (m + n) := by
  rw [terminatedAt_iff_s_none, terminatedAt_iff_s_none, of_completeQuotient_s_get?]

/-- The continued fraction of a complete quotient of `v` terminates if and only if the continued
fraction of `v` terminates. -/
theorem of_completeQuotient_terminates_iff :
    (of (completeQuotient v m)).Terminates ↔ (of v).Terminates :=
  ⟨fun ⟨n, hn⟩ ↦ ⟨m + n, of_completeQuotient_terminatedAt_iff.mp hn⟩, fun ⟨n, hn⟩ ↦
    ⟨n, of_completeQuotient_terminatedAt_iff.mpr (terminated_stable (n.le_add_left m) hn)⟩⟩

/-- The continued fraction of `v` terminates at position `n` if and only if the `n`-th complete
quotient of `v` is an integer. -/
theorem of_terminatedAt_iff_fract_completeQuotient_eq_zero :
    (of v).TerminatedAt n ↔ fract (completeQuotient v n) = 0 := by
  rw [terminatedAt_iff_s_none, ← add_zero n, ← of_completeQuotient_s_get?,
    ← terminatedAt_iff_s_none, of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none,
    IntFractPair.succ_nth_stream_eq_none_iff]
  simp [IntFractPair.stream_zero, IntFractPair.of]

/-- As long as the continued fraction of `v` has not terminated, its `n`-th partial denominator is
the integer part of the `n + 1`-th complete quotient of `v`. -/
theorem get?_of_eq_some_of_not_terminatedAt (h : ¬(of v).TerminatedAt n) :
    (of v).s.get? n = some ⟨1, ⌊completeQuotient v (n + 1)⌋⟩ := by
  rw [of_terminatedAt_iff_fract_completeQuotient_eq_zero] at h
  rw [← add_zero n, ← of_completeQuotient_s_get?, add_zero, completeQuotient_succ]
  exact of_s_head h

/-- As long as the computation of the continued fraction of `v` has not terminated, the stream of
integer and fractional parts consists of the integer and fractional parts of the complete
quotients of `v`. -/
theorem IntFractPair.stream_eq_some_of_ne_none (h : IntFractPair.stream v n ≠ none) :
    IntFractPair.stream v n = some (IntFractPair.of (completeQuotient v n)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.mp h
    obtain ⟨q, hq, -, rfl⟩ := succ_nth_stream_eq_some_iff.mp hp
    obtain rfl := Option.some.inj ((ih (hq ▸ Option.some_ne_none q)).symm.trans hq)
    rw [hp, completeQuotient_succ]
    rfl

end DivisionRing

section Field

variable {K : Type*} [Field K] [LinearOrder K] [FloorRing K] {v : K} {n : ℕ}

/-- The value `v` in terms of its `n + 1`-th complete quotient `vₙ₊₁` and of the continuants
`⟨Aₙ, Bₙ⟩` and `⟨Aₙ₋₁, Bₙ₋₁⟩` of its continued fraction:
`v = (vₙ₊₁ * Aₙ + Aₙ₋₁) / (vₙ₊₁ * Bₙ + Bₙ₋₁)`. -/
theorem eq_completeQuotient_mul_contsAux_div (h : ¬(of v).TerminatedAt n) :
    v = (completeQuotient v (n + 1) * ((of v).contsAux (n + 1)).a + ((of v).contsAux n).a) /
      (completeQuotient v (n + 1) * ((of v).contsAux (n + 1)).b + ((of v).contsAux n).b) := by
  have hs : IntFractPair.stream v n ≠ none := fun hn ↦
    h (of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none.mpr
      (IntFractPair.stream_isSeq v hn))
  rw [of_terminatedAt_iff_fract_completeQuotient_eq_zero] at h
  simpa [GenContFract.compExactValue, IntFractPair.of, h, nextConts, nextNum, nextDen,
    completeQuotient_succ] using compExactValue_correctness_of_stream_eq_some
      (IntFractPair.stream_eq_some_of_ne_none hs)

variable [IsStrictOrderedRing K]

/-- As long as the continued fraction of `v` has not terminated, the complete quotients of `v`
of positive index are greater than `1`. -/
theorem one_lt_completeQuotient_succ (h : ¬(of v).TerminatedAt n) :
    1 < completeQuotient v (n + 1) := by
  rw [of_terminatedAt_iff_fract_completeQuotient_eq_zero] at h
  rw [completeQuotient_succ]
  exact (one_lt_inv₀ ((fract_nonneg _).lt_of_ne' h)).mpr (fract_lt_one _)

/-- If `1 < v` and the continued fraction of `v` does not terminate, then all complete quotients
of `v` are greater than `1`. -/
theorem one_lt_completeQuotient (hv : ¬(of v).Terminates) (hv₁ : 1 < v) (n : ℕ) :
    1 < completeQuotient v n :=
  n.casesOn hv₁ fun n ↦ one_lt_completeQuotient_succ (not_exists.mp hv n)

/-- The denominator in `GenContFract.eq_completeQuotient_mul_contsAux_div` is positive. -/
theorem completeQuotient_mul_contsAux_b_add_pos (h : ¬(of v).TerminatedAt n) :
    0 < completeQuotient v (n + 1) * ((of v).contsAux (n + 1)).b + ((of v).contsAux n).b :=
  add_pos_of_pos_of_nonneg
    (mul_pos (zero_lt_one.trans (one_lt_completeQuotient_succ h)) of_den_pos) zero_le_of_contsAux_b

end Field

end GenContFract
