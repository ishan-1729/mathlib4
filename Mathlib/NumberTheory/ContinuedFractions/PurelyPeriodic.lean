/-
Copyright (c) 2026 Ishan Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ishan Singh
-/
module

public import Mathlib.FieldTheory.Minpoly.IsConjRoot
public import Mathlib.NumberTheory.ContinuedFractions.Lagrange

import Mathlib.Algebra.ContinuedFractions.Computation.ApproximationCorollaries
import Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat
import Mathlib.Dynamics.PeriodicPts.Defs

/-!
# Galois' theorem on purely periodic continued fractions

Let `v` be an element of a linear ordered field `K` with a floor function, for example a real
number, and assume that `v` is a quadratic irrational, that is, that the minimal polynomial of `v`
over `ℚ` has degree `2`. This polynomial has a second root `w` in `K`, the conjugate of `v`. We
prove **Galois' theorem**: the continued fraction of `v` is purely periodic if and only if `v` is
reduced, that is, `1 < v` and `-1 < w < 0`. In this case the continued fraction of `-1 / w` is
purely periodic as well, and its period is the period of `v` in reversed order.

## Main results

- `GenContFract.of_isPurelyPeriodic_iff_of_isConjRoot`: Galois' theorem, in terms of the conjugate
  `w` of `v`.
- `GenContFract.of_isPurelyPeriodic_iff_of_natDegree_minpoly_eq_two`: the continued fraction of a
  quadratic irrational `v` is purely periodic if and only if `1 < v` and `v` has a conjugate
  between `-1` and `0`.
- `GenContFract.floor_completeQuotient_neg_inv_of_isConjRoot`: if `v = [a₀; a₁, …, aₚ₋₁, a₀, …]`
  is purely periodic, then `-1 / w = [aₚ₋₁; aₚ₋₂, …, a₀, aₚ₋₁, …]`.
- `GenContFract.IsPurelyPeriodic.neg_inv_of_isConjRoot`: if the continued fraction of `v` is
  purely periodic, then so is the continued fraction of `-1 / w`.

## Implementation notes

That `w` is the conjugate of the quadratic irrational `v` is expressed as `IsConjRoot ℚ v w` and
`v ≠ w`.

The conjugate `wₙ` of the complete quotient `vₙ` of `v` is the image of `vₙ` under the homomorphism
of `ℚ`-algebras `ℚ⟮v⟯ →ₐ[ℚ] K` which maps `v` to `w`. It satisfies `wₙ₊₁ = (wₙ - ⌊vₙ⌋)⁻¹`. Hence
if `1 < vₙ` and `wₙ < 0`, then `-1 < wₙ₊₁ < 0`.

If `v` is reduced, then `-1 < wₙ < 0` and therefore `⌊vₙ⌋ = ⌊-1 / wₙ₊₁⌋` for all `n`, so that
`vₙ = ⌊vₙ⌋ + 1 / vₙ₊₁` is determined by `vₙ₊₁`. By Lagrange's theorem, two complete quotients
`v_N` and `v_{N + p}` of `v` coincide, and it follows by descending induction on `N` that
`vₚ = v`.

Conversely, let `v = vₚ` with `p > 0`, so that `1 < vₙ` for all `n`. If `0 ≤ wₙ` for all `n`, then
`⌊wₙ⌋ = ⌊vₙ⌋` for all `n`, which means that `w` and `v` have the same continued fraction and
contradicts `v ≠ w`. Hence `wₙ < 0` for some `n`, so that `-1 < wₘ < 0` for all `m > n`, and
`w = wₘ` when `m` is a multiple of `p`.

Finally, if `-1 < wₙ < 0`, then `-1 / wₙ₊₁ = ⌊vₙ⌋ + 1 / (-1 / wₙ)` with `1 < -1 / wₙ`, so that
`-1 / wₙ` is the first complete quotient of `-1 / wₙ₊₁`. This gives the reversed period.

## References

- [É. Galois, *Démonstration d'un théorème sur les fractions continues périodiques*][galois1829]

## Tags

continued fraction, purely periodic, quadratic irrational, reduced, Galois
-/

public section

open Polynomial IntermediateField Int

namespace GenContFract

open GenContFract (of)

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]
variable {v w : K} {c : ℕ → K}

/-- If `1 < x` and `y < 0`, then `-1 < (y - ⌊x⌋)⁻¹ < 0`. -/
private theorem inv_sub_floor_mem_Ioo {x y : K} (hx : 1 < x) (hy : y < 0) :
    (y - ⌊x⌋)⁻¹ ∈ Set.Ioo (-1) 0 := by
  have hk : (1 : K) ≤ ⌊x⌋ := mod_cast floor_pos.mpr hx.le
  have h : y - ⌊x⌋ < -1 := by linarith
  have h₀ : y - ⌊x⌋ < 0 := h.trans neg_one_lt_zero
  exact ⟨by rwa [← inv_neg_one, inv_lt_inv_of_neg neg_one_lt_zero h₀], inv_lt_zero.mpr h₀⟩

/-!
In the following lemmas, `c` is a sequence such that `c (n + 1) = (c n - ⌊vₙ⌋)⁻¹` for all `n`,
where `vₙ` are the complete quotients of `v`. They are applied to the sequence of the conjugates
of the complete quotients of a quadratic irrational `v`.
-/

/-- If `1 < vₙ` for all `n` and `c m < 0`, then `-1 < c n < 0` for all `n > m`. -/
private theorem mem_Ioo_of_lt (h₁ : ∀ n, 1 < completeQuotient v n)
    (hc : ∀ n, c (n + 1) = (c n - ⌊completeQuotient v n⌋)⁻¹) {m n : ℕ} (hm : c m < 0)
    (hmn : m < n) : c n ∈ Set.Ioo (-1) 0 := by
  induction n, hmn using Nat.le_induction with
  | base => exact hc m ▸ inv_sub_floor_mem_Ioo (h₁ m) hm
  | succ n _ ih => exact hc n ▸ inv_sub_floor_mem_Ioo (h₁ n) ih.2

/-- If `1 < vₙ` for all `n` and `-1 < c 0 < 0`, then `-1 < c n < 0` for all `n`. -/
private theorem mem_Ioo_of_mem_Ioo (h₁ : ∀ n, 1 < completeQuotient v n)
    (hc : ∀ n, c (n + 1) = (c n - ⌊completeQuotient v n⌋)⁻¹) (h₀ : c 0 ∈ Set.Ioo (-1) 0)
    (n : ℕ) : c n ∈ Set.Ioo (-1) 0 :=
  n.casesOn h₀ fun n ↦ mem_Ioo_of_lt h₁ hc h₀.2 n.succ_pos

/-- If `-1 < c n < 0`, then `⌊-1 / c (n + 1)⌋ = ⌊vₙ⌋`. -/
private theorem floor_neg_inv_succ (hc : ∀ n, c (n + 1) = (c n - ⌊completeQuotient v n⌋)⁻¹)
    {n : ℕ} (hn : c n ∈ Set.Ioo (-1) 0) : ⌊-(c (n + 1))⁻¹⌋ = ⌊completeQuotient v n⌋ := by
  rw [hc, inv_inv, neg_sub, floor_eq_iff]
  constructor <;> linarith [hn.1, hn.2]

/-- If `-1 < c n < 0` for all `n` and `c n` is determined by `vₙ`, then `vₙ` is determined by
`vₙ₊₁`. Hence `v` is equal to one of its complete quotients of positive index as soon as two
complete quotients of `v` coincide. -/
private theorem completeQuotient_eq_of_add_eq
    (hc : ∀ n, c (n + 1) = (c n - ⌊completeQuotient v n⌋)⁻¹) (hc₁ : ∀ n, c n ∈ Set.Ioo (-1) 0)
    (hc' : ∀ m n, completeQuotient v m = completeQuotient v n → c m = c n) {N p : ℕ}
    (h : completeQuotient v (N + p) = completeQuotient v N) : completeQuotient v p = v := by
  induction N with
  | zero => simpa using h
  | succ N ih =>
    rw [add_right_comm] at h
    refine ih ?_
    rw [← floor_add_inv_completeQuotient_succ v (N + p), ← floor_add_inv_completeQuotient_succ v N,
      h, ← floor_neg_inv_succ hc (hc₁ (N + p)), ← floor_neg_inv_succ hc (hc₁ N), hc' _ _ h]

/-- If `1 < vₙ` for all `n` and `c 0 ≠ v`, then `c n < 0` for some `n`: otherwise `c 0` and `v`
have the same continued fraction. -/
private theorem exists_lt_zero (hv : ¬(of v).Terminates) (h₁ : ∀ n, 1 < completeQuotient v n)
    (hc : ∀ n, c (n + 1) = (c n - ⌊completeQuotient v n⌋)⁻¹) (h₀ : c 0 ≠ v) : ∃ n, c n < 0 := by
  by_contra! H
  have hk (n : ℕ) : (1 : K) ≤ ⌊completeQuotient v n⌋ := mod_cast floor_pos.mpr (h₁ n).le
  have hpos (n : ℕ) : 0 < c n - ⌊completeQuotient v n⌋ := by
    have := inv_nonneg.mp (hc (n + 1) ▸ H (n + 2))
    exact inv_pos.mp (hc n ▸ by linarith [hk (n + 1)])
  have hfl (n : ℕ) : ⌊c n⌋ = ⌊completeQuotient v n⌋ :=
    floor_eq_iff.mpr ⟨by linarith [hpos n], by
      linarith [(one_lt_inv₀ (hpos n)).mp (hc n ▸ by linarith [hpos (n + 1), hk (n + 1)])]⟩
  have hcq (n : ℕ) : c n = completeQuotient (c 0) n := by
    induction n with
    | zero => rfl
    | succ n ih => rw [hc, ← hfl, completeQuotient_succ, ← ih, self_sub_floor]
  refine h₀ (of_injective ?_)
  ext1
  · simp [of_h_eq_floor, hfl 0]
  · ext1 n
    rw [get?_of_eq_some_of_not_terminatedAt (not_exists.mp hv n),
      get?_of_eq_some_of_not_terminatedAt, ← hcq, hfl]
    rw [of_terminatedAt_iff_fract_completeQuotient_eq_zero, ← hcq, ← self_sub_floor, hfl]
    exact (hpos n).ne'

omit [IsStrictOrderedRing K] in
/-- The conjugates `c n` of the complete quotients of a quadratic irrational `v` with conjugate
`w`: they are the images of the complete quotients of `v` under the homomorphism of `ℚ`-algebras
`ℚ⟮v⟯ →ₐ[ℚ] K` which maps `v` to `w`. -/
private theorem exists_conj_completeQuotient (h : (minpoly ℚ v).natDegree = 2)
    (hw : IsConjRoot ℚ v w) :
    ∃ c : ℕ → K, c 0 = w ∧ (∀ n, c (n + 1) = (c n - ⌊completeQuotient v n⌋)⁻¹) ∧
      ∀ m n, completeQuotient v m = completeQuotient v n → c m = c n := by
  have hint : IsIntegral ℚ v :=
    minpoly.ne_zero_iff.mp (ne_zero_of_natDegree_gt (one_lt_two.trans_eq h.symm))
  let φ := (algHomAdjoinIntegralEquiv ℚ hint).symm
    ⟨w, mem_aroots.mpr ⟨minpoly.ne_zero hint, hw.aeval_eq_zero⟩⟩
  refine ⟨fun n ↦ φ ⟨completeQuotient v n, completeQuotient_mem_adjoin ℚ v n⟩,
    algHomAdjoinIntegralEquiv_symm_apply_gen ℚ hint _, fun n ↦ ?_,
    fun m n hmn ↦ congrArg φ (Subtype.ext hmn)⟩
  rw [← map_intCast φ, ← map_sub, ← map_inv₀]
  exact congrArg φ (Subtype.ext (completeQuotient_succ v n))

/-- **Galois' theorem**: let `v` be a quadratic irrational and let `w ≠ v` be the conjugate of
`v`, that is, the second root of the minimal polynomial of `v` over `ℚ`. Then the continued
fraction of `v` is purely periodic if and only if `v` is reduced, that is, `1 < v` and
`-1 < w < 0`. -/
theorem of_isPurelyPeriodic_iff_of_isConjRoot (h : (minpoly ℚ v).natDegree = 2)
    (hw : IsConjRoot ℚ v w) (hvw : v ≠ w) :
    (of v).IsPurelyPeriodic ↔ 1 < v ∧ w ∈ Set.Ioo (-1) 0 := by
  have hv := (of_isEventuallyPeriodic_of_natDegree_minpoly_eq_two h).not_terminates
  obtain ⟨c, rfl, hc, hc'⟩ := exists_conj_completeQuotient h hw
  rw [of_isPurelyPeriodic_iff, and_iff_right hv]
  refine ⟨fun ⟨p, hp, hvp⟩ ↦ ?_, fun ⟨hv₁, hw₁⟩ ↦ ?_⟩
  · obtain ⟨p, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hp.ne'
    have hv₁ : 1 < v := hvp ▸ one_lt_completeQuotient_succ (not_exists.mp hv p)
    have h₁ := one_lt_completeQuotient hv hv₁
    obtain ⟨n, hn⟩ := exists_lt_zero hv h₁ hc hvw.symm
    have hper : completeQuotient v ((n + 1) * (p + 1)) = v :=
      Function.IsPeriodicPt.const_mul hvp (n + 1)
    have hn' := mem_Ioo_of_lt h₁ hc hn
      (n.lt_succ_self.trans_le (Nat.le_mul_of_pos_right _ p.succ_pos))
    rw [hc' _ 0 hper] at hn'
    exact ⟨hv₁, hn'⟩
  · obtain ⟨N, p, hp, hNp⟩ := (of_isEventuallyPeriodic_iff.mp
      (of_isEventuallyPeriodic_of_natDegree_minpoly_eq_two h)).2
    exact ⟨p, hp, completeQuotient_eq_of_add_eq hc
      (mem_Ioo_of_mem_Ioo (one_lt_completeQuotient hv hv₁) hc hw₁) hc' hNp⟩

omit [IsStrictOrderedRing K] in
/-- A quadratic irrational has a conjugate. -/
private theorem exists_ne_and_isConjRoot (h : (minpoly ℚ v).natDegree = 2) :
    ∃ w, v ≠ w ∧ IsConjRoot ℚ v w := by
  have hint : IsIntegral ℚ v :=
    minpoly.ne_zero_iff.mp (ne_zero_of_natDegree_gt (one_lt_two.trans_eq h.symm))
  have hs : ((minpoly ℚ v).map (algebraMap ℚ K)).Splits :=
    .of_natDegree_eq_two (x := v) (by rwa [natDegree_map])
      (by rw [eval_map_algebraMap, minpoly.aeval])
  exact (notMem_iff_exists_ne_and_isConjRoot (minpoly.irreducible hint).separable hs).mp
    ((minpoly.two_le_natDegree_iff hint).mp h.ge)

/-- **Galois' theorem**: the continued fraction of a quadratic irrational `v` is purely periodic if
and only if `1 < v` and the conjugate of `v` lies between `-1` and `0`. -/
theorem of_isPurelyPeriodic_iff_of_natDegree_minpoly_eq_two (h : (minpoly ℚ v).natDegree = 2) :
    (of v).IsPurelyPeriodic ↔ 1 < v ∧ ∃ w ∈ Set.Ioo (-1 : K) 0, IsConjRoot ℚ v w := by
  refine ⟨fun hv ↦ ?_, fun ⟨hv₁, w, hw₁, hw⟩ ↦ (of_isPurelyPeriodic_iff_of_isConjRoot h hw
    (hw₁.2.trans (zero_lt_one.trans hv₁)).ne').mpr ⟨hv₁, hw₁⟩⟩
  obtain ⟨w, hvw, hw⟩ := exists_ne_and_isConjRoot h
  obtain ⟨hv₁, hw₁⟩ := (of_isPurelyPeriodic_iff_of_isConjRoot h hw hvw).mp hv
  exact ⟨hv₁, w, hw₁, hw⟩

/-! ### The reversed period -/

/-- If `-1 < c n < 0`, then the first complete quotient of `-1 / c (n + 1)` is `-1 / c n`. -/
private theorem inv_fract_neg_inv_succ (hc : ∀ n, c (n + 1) = (c n - ⌊completeQuotient v n⌋)⁻¹)
    {n : ℕ} (hn : c n ∈ Set.Ioo (-1) 0) : (fract (-(c (n + 1))⁻¹))⁻¹ = -(c n)⁻¹ := by
  rw [fract, floor_neg_inv_succ hc hn, hc, inv_inv, neg_sub, sub_sub_cancel_left, inv_neg]

/-- If `-1 < c n < 0` for all `n`, then the `k`-th complete quotient of `-1 / c (m + k)` is
`-1 / c m`. -/
private theorem completeQuotient_neg_inv_add
    (hc : ∀ n, c (n + 1) = (c n - ⌊completeQuotient v n⌋)⁻¹) (hc₁ : ∀ n, c n ∈ Set.Ioo (-1) 0)
    (m k : ℕ) : completeQuotient (-(c (m + k))⁻¹) k = -(c m)⁻¹ := by
  induction k with
  | zero => rfl
  | succ k ih => rw [← add_assoc, completeQuotient_succ', inv_fract_neg_inv_succ hc (hc₁ _), ih]

/-- If `v` is a quadratic irrational with conjugate `w` and `v` is equal to its complete quotient
`vₚ₊₁`, then the conjugates of all complete quotients of `v` lie between `-1` and `0`. -/
private theorem exists_conj_completeQuotient_mem_Ioo (h : (minpoly ℚ v).natDegree = 2)
    (hw : IsConjRoot ℚ v w) (hvw : v ≠ w) {p : ℕ} (hp : completeQuotient v (p + 1) = v) :
    ∃ c : ℕ → K, c 0 = w ∧ (∀ n, c (n + 1) = (c n - ⌊completeQuotient v n⌋)⁻¹) ∧
      (∀ m n, completeQuotient v m = completeQuotient v n → c m = c n) ∧
      ∀ n, c n ∈ Set.Ioo (-1) 0 := by
  have hv := (of_isEventuallyPeriodic_of_natDegree_minpoly_eq_two h).not_terminates
  obtain ⟨hv₁, hw₁⟩ := (of_isPurelyPeriodic_iff_of_isConjRoot h hw hvw).mp
    (of_isPurelyPeriodic_iff.mpr ⟨hv, p + 1, p.succ_pos, hp⟩)
  obtain ⟨c, rfl, hc, hc'⟩ := exists_conj_completeQuotient h hw
  exact ⟨c, rfl, hc, hc', mem_Ioo_of_mem_Ioo (one_lt_completeQuotient hv hv₁) hc hw₁⟩

/-- Let `v` be a quadratic irrational with conjugate `w`. If `v` is equal to its `p`-th complete
quotient, then `-1 / w` is equal to its `p`-th complete quotient. -/
theorem completeQuotient_neg_inv_of_isConjRoot (h : (minpoly ℚ v).natDegree = 2)
    (hw : IsConjRoot ℚ v w) (hvw : v ≠ w) {p : ℕ} (hp : completeQuotient v p = v) :
    completeQuotient (-w⁻¹) p = -w⁻¹ := by
  obtain _ | p := p
  · rfl
  obtain ⟨c, rfl, hc, hc', hc₁⟩ := exists_conj_completeQuotient_mem_Ioo h hw hvw hp
  simpa only [zero_add, hc' _ 0 hp] using completeQuotient_neg_inv_add hc hc₁ 0 (p + 1)

/-- **Galois' theorem** on the reversed period: let `v = [a₀; a₁, a₂, …]` be a quadratic
irrational with conjugate `w` whose continued fraction is purely periodic with period `p`. Then
the continued fraction of `-1 / w` is `[aₚ₋₁; aₚ₋₂, …, a₀, aₚ₋₁, …]`. That is, for `j + k + 1 = p`
the integer part of the `k`-th complete quotient of `-1 / w` is the integer part of the `j`-th
complete quotient of `v`. -/
theorem floor_completeQuotient_neg_inv_of_isConjRoot (h : (minpoly ℚ v).natDegree = 2)
    (hw : IsConjRoot ℚ v w) (hvw : v ≠ w) {j k : ℕ} (hp : completeQuotient v (j + k + 1) = v) :
    ⌊completeQuotient (-w⁻¹) k⌋ = ⌊completeQuotient v j⌋ := by
  obtain ⟨c, rfl, hc, hc', hc₁⟩ := exists_conj_completeQuotient_mem_Ioo h hw hvw hp
  rw [← hc' _ 0 hp, add_right_comm, completeQuotient_neg_inv_add hc hc₁,
    floor_neg_inv_succ hc (hc₁ j)]

/-- If the continued fraction of `v` is purely periodic and `w` is the conjugate of `v`, then the
continued fraction of `-1 / w` is purely periodic. -/
theorem IsPurelyPeriodic.neg_inv_of_isConjRoot (hv : (of v).IsPurelyPeriodic)
    (hw : IsConjRoot ℚ v w) (hvw : v ≠ w) : (of (-w⁻¹)).IsPurelyPeriodic := by
  obtain ⟨-, p, hp, hvp⟩ := of_isPurelyPeriodic_iff.mp hv
  refine of_isPurelyPeriodic_iff.mpr ⟨fun ht ↦ hvw ?_, p, hp,
    completeQuotient_neg_inv_of_isConjRoot hv.isEventuallyPeriodic.natDegree_minpoly_eq_two hw hvw
      hvp⟩
  obtain ⟨q, hq⟩ := (terminates_iff_rat _).mp ht
  obtain rfl : w = algebraMap ℚ K (-q⁻¹) := by
    rw [eq_ratCast, Rat.cast_neg, Rat.cast_inv, ← hq, inv_neg, neg_neg, inv_inv]
  exact hw.symm.eq_algebraMap

end GenContFract
