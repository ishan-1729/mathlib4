/-
Copyright (c) 2026 Ishan Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ishan Singh
-/
module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.ZMod.Defs
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.GroupTheory.Solvable
public import Mathlib.SetTheory.Cardinal.Finite

import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic.LinearCombination

/-!
# Solvable transitive groups of prime degree

Let a group `G` act faithfully and transitively on a set `X` whose cardinality is a prime
number `p`. This file proves Galois's criterion for the solvability of `G`.

## Main results

* `MulAction.isSolvable_iff_exists_normal_card_eq_of_prime_card`: `G` is solvable if and only if
  it has a normal subgroup of order `p`.
* `MulAction.isSolvable_iff_forall_subsingleton_fixedBy_of_prime_card`, **Galois's criterion**:
  `G` is solvable if and only if no element of `G` other than `1` fixes two distinct points.
* `MulAction.isSolvable_iff_exists_equiv_zmod_of_prime_card`: `G` is solvable if and only if the
  points can be labelled by `ZMod p` so that every element of `G` acts as an affine map
  `k ↦ a * k + b`.

## Implementation notes

The proofs go through the existence of a normal subgroup `N` of order `p`. Such a subgroup is
cyclic and transitive, and it is its own centralizer, because an element centralizing a
transitive subgroup and fixing a point is trivial.

* If `G` is solvable, the last nontrivial term of its derived series is a commutative normal
  subgroup. It is transitive, because the action is primitive, hence it acts freely and has `p`
  elements.
* If `g` fixes two distinct points `x` and `n • x` with `n ∈ N`, then `g` commutes with `n`, hence
  with `N`, so that `g = 1`.
* If no element other than `1` fixes two points, then a point stabilizer has fewer than `p`
  elements, and Sylow's theorems show that a subgroup of order `p` is normal.
* The conjugation action embeds `G ⧸ N` in the commutative group of automorphisms of `N`.

## References

* [H. Wielandt, *Finite permutation groups*, §11][Wielandt-1964]
-/

public section

open Subgroup

namespace MulAction

variable {G X : Type*} [Group G] [MulAction G X]

/-- A subgroup of prime order `p` and of index less than `p` is normal. -/
private theorem normal_of_card_eq_of_index_lt [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {Q : Subgroup G} (hQ : Nat.card Q = p) (h : Q.index < p) : Q.Normal := by
  have hpos : 0 < Q.index := Nat.pos_of_ne_zero Q.index_ne_zero_of_finite
  let P : Sylow p G := (IsPGroup.of_card (n := 1) (by rw [hQ, pow_one])).toSylow
    fun hd ↦ (Nat.le_of_dvd hpos hd).not_gt h
  have hP : Nat.card (Sylow p G) = 1 := (card_sylow_modEq_one p G).eq_of_lt_of_lt
    ((Nat.le_of_dvd hpos P.card_dvd_index).trans_lt h) hp.out.one_lt
  have : Subsingleton (Sylow p G) := (Nat.card_eq_one_iff_unique.mp hP).1
  exact P.normal_of_subsingleton

/-- If no element other than `1` fixes two distinct points, then the stabilizer of a point has
fewer elements than there are points: it acts freely on the orbit of any other point. -/
private theorem card_stabilizer_lt [Finite X]
    (h : ∀ g : G, g ≠ 1 → (fixedBy X g).Subsingleton) {x y : X} (hxy : x ≠ y) :
    Nat.card (stabilizer G x) < Nat.card X := by
  have hf : Function.Injective fun k : stabilizer G x ↦ (k : G) • y := fun k k' hkk' ↦ by
    refine inv_mul_eq_one.mp (OneMemClass.coe_eq_one.mp (by_contra fun hne ↦ hxy (h _ hne ?_ ?_)))
    · exact mem_stabilizer_iff.mp (k⁻¹ * k').property
    · simpa [mul_smul, inv_smul_eq_iff] using hkk'.symm
  rw [← Set.ncard_range_of_injective hf]
  refine Set.ncard_lt_card fun hr ↦ ?_
  obtain ⟨k, hk⟩ := hr ▸ Set.mem_univ x
  exact hxy (smul_left_cancel (k : G) (k.property.trans hk.symm))

variable [FaithfulSMul G X]

/-- An element centralizing a transitive subgroup and fixing a point is trivial. -/
private theorem eq_one_of_mem_centralizer {N : Subgroup G} [IsPretransitive N X] {g : G}
    (hg : g ∈ centralizer (N : Set G)) {x : X} (hx : g • x = x) : g = 1 := by
  refine FaithfulSMul.eq_of_smul_eq_smul (α := X) fun y ↦ ?_
  obtain ⟨n, rfl⟩ := exists_smul_eq N x y
  rw [one_smul, Subgroup.smul_def, ← mul_smul, ← hg n n.property, mul_smul, hx]

/-- A commutative transitive subgroup acts freely. -/
private theorem isCancelSMul_of_isMulCommutative (N : Subgroup G) [IsMulCommutative N]
    [IsPretransitive N X] : IsCancelSMul N X :=
  isCancelSMul_iff_eq_one_of_smul_eq.mpr fun n _ hn ↦
    Subtype.ext (eq_one_of_mem_centralizer (le_centralizer N n.property) hn)

variable [IsPretransitive G X]

/-- A nontrivial normal subgroup of a transitive group of prime degree is transitive. -/
private theorem isPretransitive_of_normal (hp : (Nat.card X).Prime) (N : Subgroup G) [N.Normal]
    (hN : N ≠ ⊥) : IsPretransitive N X := by
  have := IsPreprimitive.of_prime_card (G := G) hp
  refine IsQuasiPreprimitive.isPretransitive_of_normal fun h ↦ hN ((eq_bot_iff_forall _).mpr ?_)
  refine fun n hn ↦ FaithfulSMul.eq_of_smul_eq_smul (α := X) fun x ↦ ?_
  rw [one_smul]
  exact (h ▸ Set.mem_univ x : x ∈ fixedPoints N X) ⟨n, hn⟩

/-- A normal subgroup of order `p` of a transitive group of prime degree `p` is transitive. -/
private theorem isPretransitive_of_normal_of_card_eq (hp : (Nat.card X).Prime) (N : Subgroup G)
    [N.Normal] (hN : Nat.card N = Nat.card X) : IsPretransitive N X :=
  isPretransitive_of_normal hp N <| by
    rintro rfl
    exact hp.one_lt.ne (by simpa using hN)

/-- If a solvable transitive group of prime degree `p` has a nontrivial normal subgroup `H`, then
it has a normal subgroup of order `p`: the last nontrivial term of the derived series of `H`. -/
private theorem exists_normal_card_eq_of_ne_bot [Finite G] [Group.IsSolvable G]
    (hp : (Nat.card X).Prime) (H : Subgroup G) (hH : H.Normal) (hH' : H ≠ ⊥) :
    ∃ N : Subgroup G, N.Normal ∧ Nat.card N = Nat.card X := by
  induction H using WellFoundedLT.induction with | ind H ih
  have := isPretransitive_of_normal hp H hH'
  by_cases h : ⁅H, H⁆ = ⊥
  · have := commutator_self_eq_bot_iff.mp h
    have := isCancelSMul_of_isMulCommutative H (X := X)
    obtain ⟨x⟩ : Nonempty X := (Nat.card_pos_iff.mp hp.pos).1
    refine ⟨H, hH, ?_⟩
    rw [← index_stabilizer_of_transitive H x, IsCancelSMul.stabilizer_eq_bot, index_bot]
  · exact ih _ (Group.IsSolvable.commutator_lt_of_ne_bot hH') (commutator_normal H H) h

/-- A solvable transitive group of prime degree `p` has a normal subgroup of order `p`. -/
private theorem exists_normal_card_eq_of_isSolvable (hp : (Nat.card X).Prime)
    [Group.IsSolvable G] : ∃ N : Subgroup G, N.Normal ∧ Nat.card N = Nat.card X := by
  have : Finite X := Nat.finite_of_card_ne_zero hp.ne_zero
  have : Finite G := .of_injective _ (toPerm_injective (α := G) (β := X))
  have : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp hp.one_lt
  obtain ⟨x, y, hxy⟩ := exists_pair_ne X
  -- the group is not trivial, because it is transitive on at least two points
  refine exists_normal_card_eq_of_ne_bot hp ⊤ inferInstance fun h ↦ hxy ?_
  obtain ⟨g, rfl⟩ := exists_smul_eq G x y
  rw [(eq_bot_iff_forall _).mp h g (mem_top g), one_smul]

/-- In a transitive group of prime degree `p` with a normal subgroup of order `p`, an element
fixing two distinct points is trivial. -/
private theorem eq_one_of_smul_eq_of_smul_eq (hp : (Nat.card X).Prime) (N : Subgroup G)
    [hN : N.Normal] (hcard : Nat.card N = Nat.card X) {g : G} {x y : X} (hxy : x ≠ y)
    (hx : g • x = x) (hy : g • y = y) : g = 1 := by
  have : Fact (Nat.card X).Prime := ⟨hp⟩
  have : IsCyclic N := isCyclic_of_prime_card hcard
  have := isPretransitive_of_normal_of_card_eq hp N hcard
  obtain ⟨n, rfl⟩ := exists_smul_eq N x y
  rw [Subgroup.smul_def] at hy
  -- `g * n * g⁻¹` and `n` are elements of `N` sending `x` to the same point, so they are equal
  have hc : (n : G)⁻¹ * (g * n * g⁻¹) = 1 :=
    eq_one_of_mem_centralizer (N := N) (x := x)
      (le_centralizer N (N.mul_mem (N.inv_mem n.property) (hN.conj_mem n n.property g)))
      (by rw [mul_smul, mul_smul, mul_smul, inv_smul_eq_iff.mpr hx.symm, hy, inv_smul_smul])
  have hng : Commute (n : G) g := (mul_inv_eq_iff_eq_mul.mp (inv_mul_eq_one.mp hc).symm).symm
  have hn : n ≠ 1 := by
    rintro rfl
    exact hxy (one_smul _ x).symm
  -- `g` commutes with the generator `n` of `N`, hence with `N`
  refine eq_one_of_mem_centralizer (N := N) (fun m hm ↦ ?_) hx
  lift m to N using hm
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp (mem_zpowers_of_prime_card (g' := m) hcard hn)
  exact (hng.zpow_left k).eq

/-- A transitive group of prime degree `p` in which no element other than `1` fixes two distinct
points has a normal subgroup of order `p`. -/
private theorem exists_normal_card_eq_of_forall_subsingleton_fixedBy (hp : (Nat.card X).Prime)
    (h : ∀ g : G, g ≠ 1 → (fixedBy X g).Subsingleton) :
    ∃ N : Subgroup G, N.Normal ∧ Nat.card N = Nat.card X := by
  have : Finite X := Nat.finite_of_card_ne_zero hp.ne_zero
  have : Finite G := .of_injective _ (toPerm_injective (α := G) (β := X))
  have : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp hp.one_lt
  have : Fact (Nat.card X).Prime := ⟨hp⟩
  obtain ⟨x, y, hxy⟩ := exists_pair_ne X
  obtain ⟨Q, hQ⟩ := Sylow.exists_subgroup_card_pow_prime (G := G) (Nat.card X) (n := 1) <| by
    rw [pow_one, ← index_stabilizer_of_transitive G x]
    exact (stabilizer G x).index_dvd_card
  rw [pow_one] at hQ
  -- the index of `Q` is the order of the stabilizer of `x`
  have hidx := Q.index_mul_card.trans (stabilizer G x).card_mul_index.symm
  rw [hQ, index_stabilizer_of_transitive] at hidx
  have hlt := card_stabilizer_lt h hxy
  rw [← Nat.eq_of_mul_eq_mul_right hp.pos hidx] at hlt
  exact ⟨Q, normal_of_card_eq_of_index_lt hQ hlt, hQ⟩

/-- A transitive group of prime degree `p` with a normal subgroup of order `p` is solvable. -/
private theorem isSolvable_of_normal_of_card_eq (hp : (Nat.card X).Prime) (N : Subgroup G)
    [N.Normal] (hN : Nat.card N = Nat.card X) : Group.IsSolvable G := by
  have : Fact (Nat.card X).Prime := ⟨hp⟩
  have : IsCyclic N := isCyclic_of_prime_card hN
  have := isPretransitive_of_normal_of_card_eq hp N hN
  have : IsMulCommutative (MulAut N) :=
    (IsCyclic.mulAutMulEquiv N).isMulCommutative.mpr inferInstance
  -- the kernel of the conjugation action of `G` on `N` is the centralizer of `N`, which is `N`
  refine Group.isSolvable_of_ker_le_range N.subtype (MulAut.conjNormal (H := N)) fun g hg ↦ ?_
  have hgN : g ∈ centralizer (N : Set G) := fun n hn ↦ by
    have := congr(($(MonoidHom.mem_ker.mp hg) ⟨n, hn⟩ : G))
    rw [MulAut.conjNormal_apply, MulAut.one_apply] at this
    exact (mul_inv_eq_iff_eq_mul.mp this).symm
  obtain ⟨x⟩ : Nonempty X := (Nat.card_pos_iff.mp hp.pos).1
  obtain ⟨n, hn⟩ := exists_smul_eq N (g • x) x
  have h1 : (n : G) * g = 1 :=
    eq_one_of_mem_centralizer (N := N) (x := x) (mul_mem (le_centralizer N n.property) hgN) <| by
      rw [mul_smul]
      exact hn
  rw [N.range_subtype, ← inv_mem_iff, ← eq_inv_of_mul_eq_one_left h1]
  exact n.property

/-- A group acting faithfully and transitively on a set of prime cardinality `p` is solvable if
and only if it has a normal subgroup of order `p`. -/
theorem isSolvable_iff_exists_normal_card_eq_of_prime_card (hp : (Nat.card X).Prime) :
    Group.IsSolvable G ↔ ∃ N : Subgroup G, N.Normal ∧ Nat.card N = Nat.card X :=
  ⟨fun _ ↦ exists_normal_card_eq_of_isSolvable hp,
    fun ⟨N, _, hN⟩ ↦ isSolvable_of_normal_of_card_eq hp N hN⟩

/-- **Galois's criterion**: a group acting faithfully and transitively on a set of prime
cardinality is solvable if and only if none of its elements other than `1` fixes two distinct
points. -/
theorem isSolvable_iff_forall_subsingleton_fixedBy_of_prime_card (hp : (Nat.card X).Prime) :
    Group.IsSolvable G ↔ ∀ g : G, g ≠ 1 → (fixedBy X g).Subsingleton := by
  rw [isSolvable_iff_exists_normal_card_eq_of_prime_card hp]
  exact ⟨fun ⟨N, _, hN⟩ g hg x hx y hy ↦
      by_contra fun hxy ↦ hg (eq_one_of_smul_eq_of_smul_eq hp N hN hxy hx hy),
    exists_normal_card_eq_of_forall_subsingleton_fixedBy hp⟩

/-! ### The affine form of the criterion -/

omit [FaithfulSMul G X] [IsPretransitive G X] in
/-- If `n ≠ 1` is an element of a subgroup `N` of order `p` acting freely on a set `X` with `p`
elements, then `k ↦ n ^ k • x` is a bijection from `ZMod p` to `X`. -/
private theorem bijective_pow_val_smul (hp : (Nat.card X).Prime) (N : Subgroup G)
    [IsCancelSMul N X] (hcard : Nat.card N = Nat.card X) {n : N} (hn : n ≠ 1) (x : X) :
    Function.Bijective fun k : ZMod (Nat.card X) ↦ n ^ k.val • x := by
  have : Fact (Nat.card X).Prime := ⟨hp⟩
  have : Finite X := Nat.finite_of_card_ne_zero hp.ne_zero
  refine (Nat.bijective_iff_injective_and_card _).mpr ⟨fun k l hkl ↦ ?_, Nat.card_zmod _⟩
  have h := IsCancelSMul.right_cancel _ _ _ hkl
  rw [pow_inj_mod, orderOf_eq_prime (hcard ▸ pow_card_eq_one') hn,
    Nat.mod_eq_of_lt (ZMod.val_lt k), Nat.mod_eq_of_lt (ZMod.val_lt l)] at h
  exact ZMod.val_injective _ h

/-- A transitive group of prime degree `p` with a normal subgroup of order `p` acts by affine
maps of `ZMod p`, for a suitable labelling of the points. -/
private theorem exists_equiv_zmod_of_normal_of_card_eq (hp : (Nat.card X).Prime)
    (N : Subgroup G) [hN : N.Normal] (hcard : Nat.card N = Nat.card X) :
    ∃ e : X ≃ ZMod (Nat.card X), ∀ g : G, ∃ a b : ZMod (Nat.card X),
      ∀ x, e (g • x) = a * e x + b := by
  have : Fact (Nat.card X).Prime := ⟨hp⟩
  have : IsCyclic N := isCyclic_of_prime_card hcard
  have := isPretransitive_of_normal_of_card_eq hp N hcard
  have := isCancelSMul_of_isMulCommutative N (X := X)
  have : Finite N := Nat.finite_of_card_ne_zero (hcard ▸ hp.ne_zero)
  have : Nontrivial N := Finite.one_lt_card_iff_nontrivial.mp (hcard ▸ hp.one_lt)
  obtain ⟨x₀⟩ : Nonempty X := (Nat.card_pos_iff.mp hp.pos).1
  obtain ⟨n, hn⟩ := exists_ne (1 : N)
  -- label the points by the exponents of `n`
  let f : ZMod (Nat.card X) → X := fun k ↦ n ^ k.val • x₀
  have hf : Function.Bijective f := bijective_pow_val_smul hp N hcard hn x₀
  have hf_nat (j : ℕ) : f j = n ^ j • x₀ := by
    dsimp only [f]
    rw [ZMod.val_natCast, ← hcard, pow_mod_natCard]
  refine ⟨(Equiv.ofBijective f hf).symm, fun g ↦ ?_⟩
  -- `g * n * g⁻¹ = n ^ a` and `g • x₀ = n ^ b • x₀`, hence `g • n ^ k • x₀ = n ^ (a * k + b) • x₀`
  obtain ⟨a, ha⟩ := (Submonoid.mem_powers_iff _ _).mp
    (mem_powers_of_prime_card (g' := (⟨g * n * g⁻¹, hN.conj_mem n n.property g⟩ : N)) hcard hn)
  obtain ⟨m, hm⟩ := exists_smul_eq N x₀ (g • x₀)
  obtain ⟨b, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp
    (mem_powers_of_prime_card (g' := m) hcard hn)
  refine ⟨a, b, fun x ↦ ?_⟩
  obtain ⟨k, rfl⟩ := hf.surjective x
  rw [Equiv.symm_apply_eq, Equiv.ofBijective_symm_apply_apply, Equiv.ofBijective_apply]
  have : (a * k + b : ZMod (Nat.card X)) = ((a * k.val + b : ℕ) : ZMod (Nat.card X)) := by
    simp
  rw [this, hf_nat, pow_add, mul_smul, hm, pow_mul, ha]
  simp [f, Subgroup.smul_def, conj_pow, mul_smul]

/-- A group acting faithfully and transitively on a set `X` of prime cardinality `p` is solvable
if and only if the points of `X` can be labelled by `ZMod p` in such a way that every element of
the group acts as an affine map `k ↦ a * k + b` (where necessarily `a ≠ 0`). -/
theorem isSolvable_iff_exists_equiv_zmod_of_prime_card {p : ℕ} [Fact p.Prime]
    (hX : Nat.card X = p) :
    Group.IsSolvable G ↔
      ∃ e : X ≃ ZMod p, ∀ g : G, ∃ a b : ZMod p, ∀ x, e (g • x) = a * e x + b := by
  subst hX
  have hp : (Nat.card X).Prime := Fact.out
  refine ⟨fun _ ↦ ?_, fun ⟨e, he⟩ ↦ ?_⟩
  · obtain ⟨N, _, hN⟩ := exists_normal_card_eq_of_isSolvable (G := G) hp
    exact exists_equiv_zmod_of_normal_of_card_eq hp N hN
  · refine (isSolvable_iff_forall_subsingleton_fixedBy_of_prime_card hp).mpr
      fun g hg x hx y hy ↦ by_contra fun hxy ↦ hg ?_
    obtain ⟨a, b, hab⟩ := he g
    have h1 := hab x
    have h2 := hab y
    rw [mem_fixedBy.mp hx] at h1
    rw [mem_fixedBy.mp hy] at h2
    -- an affine map `k ↦ a * k + b` with two fixed points is the identity
    have ha : a = 1 := by
      have : (a - 1) * (e x - e y) = 0 := by linear_combination h2 - h1
      exact sub_eq_zero.mp
        ((mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr (e.injective.ne hxy)))
    have hb : b = 0 := by simpa [ha] using h1
    refine FaithfulSMul.eq_of_smul_eq_smul (α := X) fun z ↦ e.injective ?_
    rw [hab, ha, hb, one_mul, add_zero, one_smul]

end MulAction
