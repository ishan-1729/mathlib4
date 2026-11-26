/-
Copyright (c) 2026 Ishan Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ishan Singh
-/
module

public import Mathlib.NumberTheory.ContinuedFractions.QuadraticIrrational

import Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Lemmas
import Mathlib.RingTheory.Localization.Integral

/-!
# Lagrange's theorem on periodic continued fractions

Let `v` be an element of a linear ordered field `K` with a floor function, for example a real
number. We prove **Lagrange's theorem**: if `v` is a quadratic irrational, that is, if the minimal
polynomial of `v` over `ℚ` has degree `2`, then the continued fraction of `v` is eventually
periodic. Together with Euler's theorem, this shows that the continued fraction of `v` is
eventually periodic if and only if `v` is a quadratic irrational.

## Main results

- `GenContFract.of_isEventuallyPeriodic_of_natDegree_minpoly_eq_two`: Lagrange's theorem.
- `GenContFract.of_isEventuallyPeriodic_iff_natDegree_minpoly_eq_two`: the continued fraction of
  `v` is eventually periodic if and only if the minimal polynomial of `v` over `ℚ` has degree `2`.

## Implementation notes

We follow the proof of Steinig [steinig1992]. If the complete quotient `vₙ` of `v` is a root of
the polynomial `A X² + B X + C` with integer coefficients, then `vₙ₊₁` is a root of
`(A k² + B k + C) X² + (2 A k + B) X + A`, where `k = ⌊vₙ⌋`. This gives polynomials
`Aₙ X² + Bₙ X + Cₙ` with root `vₙ`, all of the same discriminant `D`. If `0 ≤ Aₙ * Cₙ` and
`0 ≤ Aₙ₊₁ * Cₙ₊₁` for some `n ≥ 1`, then `|Bₙ₊₁| < |Bₙ|`. Hence `Aₙ * Cₙ < 0` for infinitely
many `n`. For these `n`, the absolute values of `Aₙ`, `Bₙ` and `Cₙ` are at most `D` and `vₙ` is
the only positive root of `Aₙ X² + Bₙ X + Cₙ`, so that only finitely many values of `vₙ` are
possible. Therefore two complete quotients of `v` coincide.

## References

- [G. H. Hardy and E. M. Wright, *An Introduction to the Theory of Numbers*, Theorem 177]
  [hardy2008introduction]
- [J. Steinig, *A proof of Lagrange's theorem on periodic continued fractions*][steinig1992]

## Tags

continued fraction, periodic, quadratic irrational, Lagrange
-/

public section

open Polynomial Int

namespace GenContFract

open GenContFract (of)

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]
variable {v x y : K} {A B C : ℤ}

/-- A polynomial `A X² + B X + C` with `A * C < 0` has at most one positive root. -/
private theorem eq_of_quadratic_eq_zero_of_mul_neg (hAC : A * C < 0) (hx : 0 < x) (hy : 0 < y)
    (hx₀ : A * x ^ 2 + B * x + C = 0) (hy₀ : A * y ^ 2 + B * y + C = 0) : x = y := by
  by_contra hxy
  have h : (A : K) * (x + y) + B = 0 :=
    mul_left_cancel₀ (sub_ne_zero.mpr hxy) (by linear_combination hx₀ - hy₀)
  have hAC' : (A * C : K) < 0 := mod_cast hAC
  rw [show (A * C : K) = A ^ 2 * (x * y) by linear_combination A * hx₀ - A * x * h] at hAC'
  exact hAC'.not_ge (by positivity)

/-- The coefficients of a polynomial `A X² + B X + C` with `A * C < 0` are bounded by its
discriminant. -/
private theorem abs_le_discrim_of_mul_neg (hAC : A * C < 0) :
    |A| ≤ discrim A B C ∧ |B| ≤ discrim A B C ∧ |C| ≤ discrim A B C := by
  have h : |A| * |C| = -(A * C) := by rw [← abs_mul, abs_of_neg hAC]
  have hA : |A| ≤ |A| * |C| :=
    le_mul_of_one_le_right (abs_nonneg A) (one_le_abs (right_ne_zero_of_mul hAC.ne))
  have hC : |C| ≤ |A| * |C| :=
    le_mul_of_one_le_left (abs_nonneg C) (one_le_abs (left_ne_zero_of_mul hAC.ne))
  have hB : |B| ≤ B ^ 2 := by simpa using natAbs_le_self_sq B
  rw [discrim]
  refine ⟨?_, ?_, ?_⟩ <;> linarith [sq_nonneg B]

/-- There are only finitely many positive roots of polynomials `A X² + B X + C` with integer
coefficients, `A * C < 0` and discriminant `D`. -/
private theorem finite_setOf_quadratic_eq_zero (D : ℤ) :
    {x : K | 0 < x ∧ ∃ A B C : ℤ, A * C < 0 ∧ discrim A B C = D ∧
      A * x ^ 2 + B * x + C = 0}.Finite := by
  refine ((Set.finite_Icc (-D, -D, -D) (D, D, D)).biUnion fun T _ ↦ Set.Subsingleton.finite
    (s := {x : K | 0 < x ∧ T.1 * T.2.2 < 0 ∧ T.1 * x ^ 2 + T.2.1 * x + T.2.2 = 0}) ?_).subset ?_
  · rintro x ⟨hx, hT, hx₀⟩ y ⟨hy, -, hy₀⟩
    exact eq_of_quadratic_eq_zero_of_mul_neg hT hx hy hx₀ hy₀
  · rintro x ⟨hx, A, B, C, hAC, rfl, hx₀⟩
    obtain ⟨hA, hB, hC⟩ := abs_le_discrim_of_mul_neg (B := B) hAC
    exact Set.mem_biUnion (x := (A, B, C))
      ⟨⟨(abs_le.mp hA).1, (abs_le.mp hB).1, (abs_le.mp hC).1⟩,
        (abs_le.mp hA).2, (abs_le.mp hB).2, (abs_le.mp hC).2⟩ ⟨hx, hAC, hx₀⟩

/-- If a polynomial `A X² + B X + C` with `0 ≤ A * C` has a positive root, then `A` and `B` have
opposite signs. -/
private theorem mul_neg_of_quadratic_eq_zero (hA : A ≠ 0) (hAC : 0 ≤ A * C) (hx : 0 < x)
    (hx₀ : A * x ^ 2 + B * x + C = 0) : A * B < 0 := by
  have hAC' : (0 : K) ≤ A * C := mod_cast hAC
  have h : (A * B : K) * x < 0 := by
    rw [show (A * B : K) * x = -(A ^ 2 * x ^ 2 + A * C) by linear_combination A * hx₀]
    exact neg_neg_of_pos (by positivity)
  have h' : (A * B : K) < 0 := neg_of_mul_neg_left h hx.le
  exact mod_cast h'

/-- If `v` is an irrational root of `A X² + B X + C`, then its first complete quotient is a root
of `(A k² + B k + C) X² + (2 A k + B) X + A`, where `k = ⌊v⌋`, and the leading coefficient of
this polynomial is nonzero. -/
private theorem quadratic_completeQuotient_one (hv : ¬(of v).Terminates) (hA : A ≠ 0)
    (h : A * v ^ 2 + B * v + C = 0) :
    A * ⌊v⌋ ^ 2 + B * ⌊v⌋ + C ≠ 0 ∧
      ((A * ⌊v⌋ ^ 2 + B * ⌊v⌋ + C : ℤ) : K) * completeQuotient v 1 ^ 2 +
        ((2 * A * ⌊v⌋ + B : ℤ) : K) * completeQuotient v 1 + A = 0 := by
  have hv₀ : fract v ≠ 0 :=
    (of_terminatedAt_iff_fract_completeQuotient_eq_zero (n := 0)).not.mp (not_exists.mp hv 0)
  refine ⟨fun h₀ ↦ ?_, ?_⟩
  · have h₀' : (A : K) * ⌊v⌋ ^ 2 + B * ⌊v⌋ + C = 0 := mod_cast h₀
    have key : (A : K) * (v + ⌊v⌋) + B = 0 :=
      mul_left_cancel₀ hv₀ (by rw [fract]; linear_combination h - h₀')
    have hA' : (A : K) ≠ 0 := mod_cast hA
    refine hv ((terminates_iff_rat v).mpr ⟨-B / A - ⌊v⌋, ?_⟩)
    push_cast
    field_simp
    linear_combination key
  · rw [completeQuotient_succ, completeQuotient_zero]
    rw [fract] at hv₀ ⊢
    push_cast
    field_simp
    linear_combination h

/-- The complete quotients of an irrational root of a quadratic polynomial with integer
coefficients are roots of quadratic polynomials with integer coefficients and the same
discriminant. -/
private theorem exists_quadratic_completeQuotient (hv : ¬(of v).Terminates) (hA : A ≠ 0)
    (h : A * v ^ 2 + B * v + C = 0) (n : ℕ) :
    ∃ A' B' C' : ℤ, A' ≠ 0 ∧ discrim A' B' C' = discrim A B C ∧
      A' * completeQuotient v n ^ 2 + B' * completeQuotient v n + C' = 0 := by
  induction n generalizing v A B C with
  | zero => exact ⟨A, B, C, hA, rfl, h⟩
  | succ n ih =>
    obtain ⟨hA', h'⟩ := quadratic_completeQuotient_one hv hA h
    obtain ⟨A', B', C', hA', hD, h'⟩ := ih (of_completeQuotient_terminates_iff.not.mpr hv) hA' h'
    exact ⟨A', B', C', hA', hD.trans (by rw [discrim, discrim]; ring), h'⟩

/-- If `v > 1` is an irrational root of a quadratic polynomial with integer coefficients, then
some complete quotient of `v` is a root of a polynomial `A' X² + B' X + C'` with integer
coefficients, `A' * C' < 0` and the same discriminant. -/
private theorem exists_completeQuotient_quadratic_mul_neg (hv : ¬(of v).Terminates) (hv₁ : 1 < v)
    (hA : A ≠ 0) (h : A * v ^ 2 + B * v + C = 0) :
    ∃ n, 0 < completeQuotient v n ∧ ∃ A' B' C' : ℤ, A' * C' < 0 ∧
      discrim A' B' C' = discrim A B C ∧
        A' * completeQuotient v n ^ 2 + B' * completeQuotient v n + C' = 0 := by
  induction hB : B.natAbs using Nat.strong_induction_on generalizing v A B C with | _ b ih
  subst hB
  have hv₀ : 0 < v := zero_lt_one.trans hv₁
  rcases lt_or_ge (A * C) 0 with hAC | hAC
  · exact ⟨0, hv₀, A, B, C, hAC, rfl, h⟩
  obtain ⟨hA', h'⟩ := quadratic_completeQuotient_one hv hA h
  have hv' : ¬(of (completeQuotient v 1)).Terminates :=
    of_completeQuotient_terminates_iff.not.mpr hv
  have hv₁' : 1 < completeQuotient v 1 := one_lt_completeQuotient_succ (not_exists.mp hv 0)
  have hD : discrim (A * ⌊v⌋ ^ 2 + B * ⌊v⌋ + C) (2 * A * ⌊v⌋ + B) A = discrim A B C := by
    rw [discrim, discrim]
    ring
  rcases lt_or_ge ((A * ⌊v⌋ ^ 2 + B * ⌊v⌋ + C) * A) 0 with hAA | hAA
  · exact ⟨1, zero_lt_one.trans hv₁', _, _, _, hAA, hD, h'⟩
  -- Otherwise `B` and `2 * A * ⌊v⌋ + B` both have the sign opposite to `A`, so that
  -- `|2 * A * ⌊v⌋ + B| < |B|`, and we conclude by induction.
  have hk : 0 < ⌊v⌋ := floor_pos.mpr hv₁.le
  have hAB := mul_neg_of_quadratic_eq_zero hA hAC hv₀ h
  have hAB' := mul_neg_of_quadratic_eq_zero (x := fract v) (B := 2 * A * ⌊v⌋ + B)
    (C := A * ⌊v⌋ ^ 2 + B * ⌊v⌋ + C) hA (by rwa [mul_comm])
    (inv_pos.mp (zero_lt_one.trans hv₁')) (by rw [fract]; push_cast; linear_combination h)
  have hlt : (2 * A * ⌊v⌋ + B).natAbs < B.natAbs := natAbs_lt_iff_sq_lt.mpr <| by
    nlinarith [mul_pos hk (neg_pos.mpr hAB), mul_pos hk (neg_pos.mpr hAB')]
  obtain ⟨n, hn, A', B', C', hAC', hD', hn'⟩ := ih _ hlt hv' hv₁' hA' h' rfl
  exact ⟨n + 1, hn, A', B', C', hAC', hD'.trans hD, hn'⟩

/-- Two complete quotients of an irrational root of a quadratic polynomial with integer
coefficients coincide. -/
private theorem exists_completeQuotient_add_eq (hv : ¬(of v).Terminates) (hA : A ≠ 0)
    (h : A * v ^ 2 + B * v + C = 0) :
    ∃ N p, 0 < p ∧ completeQuotient v (N + p) = completeQuotient v N := by
  by_contra! H
  have hinj : Function.Injective (completeQuotient v) := .of_lt_imp_ne fun m n hmn heq ↦
    H m (n - m) (Nat.sub_pos_of_lt hmn) (by rw [Nat.add_sub_cancel' hmn.le, heq])
  refine ((finite_setOf_quadratic_eq_zero (discrim A B C)).preimage hinj.injOn).not_infinite
    (Set.infinite_of_forall_exists_gt fun N ↦ ?_)
  obtain ⟨A', B', C', hA', hD, h'⟩ := exists_quadratic_completeQuotient hv hA h (N + 1)
  obtain ⟨n, hn, A'', B'', C'', hAC, hD', hn'⟩ := exists_completeQuotient_quadratic_mul_neg
    (of_completeQuotient_terminates_iff.not.mpr hv)
    (one_lt_completeQuotient_succ (not_exists.mp hv N)) hA' h'
  rw [← completeQuotient_add] at hn hn'
  exact ⟨n + (N + 1), ⟨hn, A'', B'', C'', hAC, hD'.trans hD, hn'⟩, by lia⟩

/-- A quadratic irrational is a root of a quadratic polynomial with integer coefficients. -/
private theorem exists_int_quadratic_eq_zero (h : (minpoly ℚ v).natDegree = 2) :
    ∃ A B C : ℤ, A ≠ 0 ∧ (A : K) * v ^ 2 + B * v + C = 0 := by
  set P := IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ v)
  have hP : P.natDegree < 3 := Nat.lt_succ_of_le <| natDegree_le_iff_coeff_eq_zero.mpr fun n hn ↦
    (IsFractionRing.coeff_integerNormalization_eq_zero_iff _ n).mpr
      (coeff_eq_zero_of_natDegree_lt (h ▸ hn))
  have hv : aeval v P = 0 :=
    IsLocalization.integerNormalization_aeval_eq_zero _ _ (minpoly.aeval ℚ v)
  refine ⟨P.coeff 2, P.coeff 1, P.coeff 0, ?_, ?_⟩
  · rw [Ne, IsFractionRing.coeff_integerNormalization_eq_zero_iff, ← h, coeff_natDegree,
      leadingCoeff_eq_zero]
    exact ne_zero_of_natDegree_gt (n := 1) (by lia)
  · rw [aeval_eq_sum_range' hP] at hv
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zsmul_eq_mul] at hv
    linear_combination hv

/-- **Lagrange's theorem**: if `v` is a quadratic irrational, that is, if the minimal polynomial
of `v` over `ℚ` has degree `2`, then the continued fraction of `v` is eventually periodic. -/
theorem of_isEventuallyPeriodic_of_natDegree_minpoly_eq_two (h : (minpoly ℚ v).natDegree = 2) :
    (of v).IsEventuallyPeriodic := by
  have hv : ¬(of v).Terminates := fun hv ↦ by
    obtain ⟨q, rfl⟩ := (terminates_iff_rat v).mp hv
    have := (minpoly.natDegree_eq_one_iff (A := ℚ) (x := (q : K))).mpr ⟨q, rfl⟩
    lia
  obtain ⟨A, B, C, hA, hABC⟩ := exists_int_quadratic_eq_zero h
  exact of_isEventuallyPeriodic_iff.mpr ⟨hv, exists_completeQuotient_add_eq hv hA hABC⟩

/-- The continued fraction of `v` is eventually periodic if and only if `v` is a quadratic
irrational, that is, if and only if the minimal polynomial of `v` over `ℚ` has degree `2`. -/
theorem of_isEventuallyPeriodic_iff_natDegree_minpoly_eq_two :
    (of v).IsEventuallyPeriodic ↔ (minpoly ℚ v).natDegree = 2 :=
  ⟨IsEventuallyPeriodic.natDegree_minpoly_eq_two,
    of_isEventuallyPeriodic_of_natDegree_minpoly_eq_two⟩

end GenContFract
