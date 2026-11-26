/-
Copyright (c) 2026 Ishan Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ishan Singh
-/
module

public import Mathlib.FieldTheory.PolynomialGaloisGroup
public import Mathlib.GroupTheory.Solvable

import Mathlib.GroupTheory.GroupAction.PrimeDegree

/-!
# Galois's criterion for polynomials of prime degree

Let `f` be an irreducible polynomial of prime degree over a field `F`. This file proves Galois's
criterion: the Galois group of `f` is solvable if and only if any two distinct roots of `f`
generate its splitting field, that is, if and only if every root of `f` is a rational function of
any two of them.

Here solvability refers to the Galois group: the relation with solvability by radicals is not
treated in this file.

## Main results

* `Polynomial.Gal.isSolvable_iff_forall_adjoin_pair_eq_top_of_prime_degree`: if `E` is a splitting
  field of `f`, then `f.Gal` is solvable if and only if `F⟮x, y⟯ = ⊤` for all roots `x ≠ y` of `f`
  in `E`.
* `Polynomial.Gal.isSolvable_iff_forall_rootSet_subset_adjoin_pair_of_prime_degree`: if `f` splits
  in an extension `E` of `F`, then `f.Gal` is solvable if and only if all roots of `f` in `E` lie
  in `F⟮x, y⟯`, for all roots `x ≠ y` of `f` in `E`.

## Implementation notes

If `f` is separable, the Galois group of a splitting field `E` of `f` acts faithfully and
transitively on the roots of `f` in `E`, and the number of roots is the degree of `f`. By
`MulAction.isSolvable_iff_forall_subsingleton_fixedBy_of_prime_card`, this group is solvable if and
only if none of its elements other than `1` fixes two distinct roots. By the Galois
correspondence, the latter means that two distinct roots generate `E`. The criterion is applied
to `Gal(E/F)` rather than to `f.Gal` acting through `Polynomial.Gal.galAction`, because the Galois
correspondence is stated for `Gal(E/F)`.

If `f` is not separable, then it has only one root, so that its Galois group is trivial and both
conditions hold.

## References

* [É. Galois, *Mémoire sur les conditions de résolubilité des équations par radicaux*,
  Proposition VIII][galois1846]
-/

public section

open IntermediateField MulAction

namespace Polynomial.Gal

variable {F E : Type*} [Field F] [Field E] [Algebra F E] {f : F[X]}

/-- The Galois group of a splitting field of `f` acts faithfully on the roots of `f`. -/
private theorem faithfulSMul_rootSet [f.IsSplittingField F E] :
    FaithfulSMul Gal(E/F) (f.rootSet E) where
  eq_of_smul_eq_smul h := AlgEquiv.coe_toAlgHom_injective <|
    AlgHom.ext_of_adjoin_eq_top (IsSplittingField.adjoin_rootSet E f)
      fun x hx ↦ congr(($(h ⟨x, hx⟩) : E))

/-- The Galois group of a splitting field of an irreducible polynomial `f` acts transitively on
the roots of `f`. -/
private theorem isPretransitive_rootSet [f.IsSplittingField F E] (hf : Irreducible f) :
    IsPretransitive Gal(E/F) (f.rootSet E) where
  exists_smul_eq x y := by
    have : Fact (f.map (algebraMap F E)).Splits := ⟨IsSplittingField.splits E f⟩
    have := Normal.of_isSplittingField (F := F) (E := E) f
    obtain ⟨g, hg⟩ := (galAction_isPretransitive f E hf).exists_smul_eq x y
    obtain ⟨σ, rfl⟩ := restrict_surjective f E g
    exact ⟨σ, Subtype.ext ((restrict_smul σ x).symm.trans congr(($hg : E)))⟩

/-- A subset `S` of a finite Galois extension generates it if and only if no automorphism other
than `1` fixes all elements of `S`. -/
private theorem adjoin_eq_top_iff_forall_eq_one [FiniteDimensional F E] [IsGalois F E]
    {S : Set E} : adjoin F S = ⊤ ↔ ∀ σ : Gal(E/F), (∀ x ∈ S, σ x = x) → σ = 1 := by
  rw [← fixedField_bot, eq_comm, IsGalois.fixedField_eq_iff_fixingSubgroup_eq,
    Subgroup.eq_bot_iff_forall]
  refine forall_congr' fun σ ↦ imp_congr_left ?_
  simpa only [IntermediateField.mem_fixingSubgroup_iff, AlgEquiv.smul_def] using
    forall_mem_adjoin_smul_eq_self_iff F (S := S) σ

/-- An inseparable irreducible polynomial of prime degree has at most one root. -/
private theorem subsingleton_rootSet_of_not_separable (hf : Irreducible f) (hp : f.natDegree.Prime)
    (hsep : ¬f.Separable) (hE : (f.map (algebraMap F E)).Splits) :
    (f.rootSet E).Subsingleton := by
  classical
  have h := (Nat.dvd_prime hp).mp hf.natSepDegree_dvd_natDegree
  rw [natSepDegree_eq_natDegree_iff f hf.ne_zero, or_iff_left hsep,
    natSepDegree_eq_of_splits f hE] at h
  rw [rootSet_def]
  exact fun x hx y hy ↦ Finset.card_le_one.mp h.le x hx y hy

/-- **Galois's criterion** for the Galois group of a splitting field `E` of a separable
polynomial `f`. -/
private theorem isSolvable_iff_of_separable [f.IsSplittingField F E] (hf : Irreducible f)
    (hsep : f.Separable) (hp : f.natDegree.Prime) :
    Group.IsSolvable Gal(E/F) ↔
      ∀ x ∈ f.rootSet E, ∀ y ∈ f.rootSet E, x ≠ y → F⟮x, y⟯ = ⊤ := by
  have := IsSplittingField.finiteDimensional E f
  have := IsGalois.of_separable_splitting_field (E := E) hsep
  have := faithfulSMul_rootSet (E := E) (f := f)
  have := isPretransitive_rootSet (E := E) hf
  have hcard : Nat.card (f.rootSet E) = f.natDegree :=
    Nat.card_eq_fintype_card.trans (card_rootSet_eq_natDegree hsep (IsSplittingField.splits E f))
  rw [isSolvable_iff_forall_subsingleton_fixedBy_of_prime_card (X := f.rootSet E) (hcard ▸ hp)]
  simp_rw [adjoin_eq_top_iff_forall_eq_one, Set.forall_mem_insert, Set.forall_mem_singleton]
  constructor
  · intro h x hx y hy hxy σ hσ
    by_contra hσ1
    exact hxy congr(($(h σ hσ1 (x := ⟨x, hx⟩) (Subtype.ext hσ.1) (y := ⟨y, hy⟩)
      (Subtype.ext hσ.2)) : E))
  · intro h σ hσ x hx y hy
    by_contra hxy
    exact hσ (h x x.property y y.property (Subtype.coe_ne_coe.mpr hxy) σ
      ⟨congr(($hx : E)), congr(($hy : E))⟩)

/-- **Galois's criterion**: the Galois group of an irreducible polynomial `f` of prime degree is
solvable if and only if any two distinct roots of `f` generate its splitting field `E` (for
instance `E = f.SplittingField`). If `f` is not separable, then it has only one root and both
conditions hold. -/
theorem isSolvable_iff_forall_adjoin_pair_eq_top_of_prime_degree [f.IsSplittingField F E]
    (hf : Irreducible f) (hp : f.natDegree.Prime) :
    Group.IsSolvable f.Gal ↔ ∀ x ∈ f.rootSet E, ∀ y ∈ f.rootSet E, x ≠ y → F⟮x, y⟯ = ⊤ := by
  -- the Galois group of `E` is isomorphic to that of `f`
  let e : Gal(E/F) ≃* f.Gal := (IsSplittingField.algEquiv E f).autCongr
  have he : Group.IsSolvable f.Gal ↔ Group.IsSolvable Gal(E/F) :=
    ⟨fun _ ↦ Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective,
      fun _ ↦ Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective⟩
  rw [he]
  by_cases hsep : f.Separable
  · exact isSolvable_iff_of_separable hf hsep hp
  -- if `f` is not separable, it has only one root and the Galois group of `E` is trivial
  have h := subsingleton_rootSet_of_not_separable hf hp hsep (IsSplittingField.splits E f)
  have := faithfulSMul_rootSet (E := E) (f := f)
  have : Subsingleton Gal(E/F) := ⟨fun σ τ ↦ FaithfulSMul.eq_of_smul_eq_smul (α := f.rootSet E)
    fun x ↦ Subtype.ext (h (σ • x).property (τ • x).property)⟩
  exact iff_of_true inferInstance fun x hx y hy hxy ↦ (hxy (h hx hy)).elim

/-- **Galois's criterion**: the Galois group of an irreducible polynomial `f` of prime degree is
solvable if and only if every root of `f` is a rational function of any two distinct roots. Here
the roots are taken in any extension `E` in which `f` splits. -/
theorem isSolvable_iff_forall_rootSet_subset_adjoin_pair_of_prime_degree (hf : Irreducible f)
    (hp : f.natDegree.Prime) (hE : (f.map (algebraMap F E)).Splits) :
    Group.IsSolvable f.Gal ↔
      ∀ x ∈ f.rootSet E, ∀ y ∈ f.rootSet E, x ≠ y → f.rootSet E ⊆ F⟮x, y⟯ := by
  -- the roots of `f` in `E` are those in the splitting field `K` generated by them
  let K := adjoin F (f.rootSet E)
  have : f.IsSplittingField F K := adjoin_rootSet_isSplittingField hE
  have hroot (x : K) : x ∈ f.rootSet K ↔ (x : E) ∈ f.rootSet E := by
    simp [mem_rootSet]
  have key (x y : K) : F⟮x, y⟯ = ⊤ ↔ f.rootSet E ⊆ F⟮(x : E), (y : E)⟯ := by
    rw [← lift_inj, lift_adjoin, lift_top, Set.image_pair, ← adjoin_le_iff (S := f.rootSet E)]
    exact ⟨ge_of_eq,
      fun h ↦ le_antisymm (adjoin_le_iff.mpr (Set.pair_subset x.property y.property)) h⟩
  rw [isSolvable_iff_forall_adjoin_pair_eq_top_of_prime_degree (E := K) hf hp]
  constructor
  · intro h x hx y hy hxy
    exact (key ⟨x, subset_adjoin F _ hx⟩ ⟨y, subset_adjoin F _ hy⟩).mp
      (h _ ((hroot _).mpr hx) _ ((hroot _).mpr hy) (by simpa using hxy))
  · intro h x hx y hy hxy
    exact (key x y).mpr (h _ ((hroot x).mp hx) _ ((hroot y).mp hy) (Subtype.coe_ne_coe.mpr hxy))

end Polynomial.Gal
