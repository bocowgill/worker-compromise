/-
Copyright 2026 The Market First Bridge Contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib
public import WorkerCompromiseProof.Core.SwitchingCostMatching

/-!
# Stable matching existence with more workers than firms

The offer/rejection fixed-point proof extends to rectangular markets. If a firm were
unmatched, every worker would be matched, giving an injection from workers to firms.
This contradicts the strict inequality of the population sizes.
-/

@[expose] public section

namespace WorkerCompromiseProof.Imbalanced

open Set SwitchingCostMatching

private def firmKey {n w : ℕ} (p : Profile n w) (i : Fin n) (j : Fin w) : ℝ ×ₗ Fin w :=
  toLex (p (false, i, j), j)

private def workerKey {n w : ℕ} (p : Profile n w) (i : Fin n) (j : Fin w) : ℝ ×ₗ Fin n :=
  toLex (p (true, i, j), i)

private def rejectF {n w : ℕ} (p : Profile n w) (A : Set (Fin n × Fin w)) :
    Set (Fin n × Fin w) :=
  {e | e ∈ A ∧ ∃ j, (e.1, j) ∈ A ∧ firmKey p e.1 e.2 < firmKey p e.1 j}

private def rejectW {n w : ℕ} (p : Profile n w) (B : Set (Fin n × Fin w)) :
    Set (Fin n × Fin w) :=
  {e | e ∈ B ∧ ∃ i, (i, e.2) ∈ B ∧ workerKey p e.1 e.2 < workerKey p i e.2}

private theorem rejectF_mono {n w : ℕ} (p : Profile n w) : Monotone (rejectF p) := by
  intro A B h e he
  obtain ⟨he, j, hj, hlt⟩ := he
  exact ⟨h he, j, h hj, hlt⟩

private theorem rejectW_mono {n w : ℕ} (p : Profile n w) : Monotone (rejectW p) := by
  intro A B h e he
  obtain ⟨he, i, hi, hlt⟩ := he
  exact ⟨h he, i, h hi, hlt⟩

private def offerMap {n w : ℕ} (p : Profile n w) :
    Set (Fin n × Fin w) →o Set (Fin n × Fin w) where
  toFun A := (rejectW p (rejectF p A)ᶜ)ᶜ
  monotone' := fun _ _ h ↦ compl_subset_compl.mpr
    (rejectW_mono p (compl_subset_compl.mpr (rejectF_mono p h)))

private theorem fixed_offers {n w : ℕ} (p : Profile n w) :
    ∃ A B : Set (Fin n × Fin w), B = (rejectF p A)ᶜ ∧ A = (rejectW p B)ᶜ := by
  refine ⟨(offerMap p).lfp, (rejectF p (offerMap p).lfp)ᶜ, rfl, ?_⟩
  exact (offerMap p).map_lfp.symm

private theorem matching_of_fixed_offers {n w : ℕ} (p : Profile n w)
    (A B : Set (Fin n × Fin w)) (hB : B = (rejectF p A)ᶜ)
    (hA : A = (rejectW p B)ᶜ) (hcard : n < w) :
    ∃ m : Matching n w, (∀ i, (i, m i) ∈ A ∩ B) ∧
      ∀ i j, (i, j) ∈ A ∩ B → m i = j := by
  classical
  have hrow : ∀ i j k, (i, j) ∈ A ∩ B → (i, k) ∈ A ∩ B → j = k := by
    intro i j k hj hk
    have hnj : (i, j) ∉ rejectF p A := by simpa only [hB, mem_compl_iff] using hj.2
    have hnk : (i, k) ∉ rejectF p A := by simpa only [hB, mem_compl_iff] using hk.2
    have he : firmKey p i j = firmKey p i k := le_antisymm
      (le_of_not_gt fun h ↦ hnk ⟨hk.1, j, hj.1, h⟩)
      (le_of_not_gt fun h ↦ hnj ⟨hj.1, k, hk.1, h⟩)
    exact congrArg (fun x : ℝ ×ₗ Fin w ↦ (ofLex x).2) he
  have hcol : ∀ i k j, (i, j) ∈ A ∩ B → (k, j) ∈ A ∩ B → i = k := by
    intro i k j hi hk
    have hni : (i, j) ∉ rejectW p B := by simpa only [hA, mem_compl_iff] using hi.1
    have hnk : (k, j) ∉ rejectW p B := by simpa only [hA, mem_compl_iff] using hk.1
    have he : workerKey p i j = workerKey p k j := le_antisymm
      (le_of_not_gt fun h ↦ hnk ⟨hk.2, i, hi.2, h⟩)
      (le_of_not_gt fun h ↦ hni ⟨hi.2, k, hk.2, h⟩)
    exact congrArg (fun x : ℝ ×ₗ Fin n ↦ (ofLex x).2) he
  have hfirm : ∀ i, (∃ j, (i, j) ∈ A) → ∃ j, (i, j) ∈ A ∩ B := by
    intro i hi
    obtain ⟨j, hj, hmax⟩ := Set.exists_max_image {j | (i, j) ∈ A}
      (firmKey p i) (Set.toFinite _) hi
    refine ⟨j, hj, ?_⟩
    rw [hB]
    exact fun h ↦ (not_lt_of_ge (hmax h.2.choose h.2.choose_spec.1)) h.2.choose_spec.2
  have hworker : ∀ j, (∃ i, (i, j) ∈ B) → ∃ i, (i, j) ∈ A ∩ B := by
    intro j hj
    obtain ⟨i, hi, hmax⟩ := Set.exists_max_image {i | (i, j) ∈ B}
      (fun i ↦ workerKey p i j) (Set.toFinite _) hj
    refine ⟨i, ?_, hi⟩
    rw [hA]
    exact fun h ↦ (not_lt_of_ge (hmax h.2.choose h.2.choose_spec.1)) h.2.choose_spec.2
  have hall : ∀ i, ∃ j, (i, j) ∈ A ∩ B := by
    intro i
    by_contra hi
    have hnotA : ∀ j, (i, j) ∉ A := fun j hj ↦ hi (hfirm i ⟨j, hj⟩)
    have hcols : ∀ j, ∃ k, (k, j) ∈ A ∩ B := by
      intro j
      apply hworker j
      have hrej : (i, j) ∈ rejectW p B := by
        simpa only [hA, mem_compl_iff, not_not] using hnotA j
      exact ⟨i, hrej.1⟩
    choose f hf using hcols
    have hinj : Function.Injective f := fun j k h ↦
      hrow (f j) j k (hf j) (h ▸ hf k)
    have hle := Fintype.card_le_of_injective f hinj
    simp only [Fintype.card_fin] at hle
    omega
  choose f hf using hall
  have hinj : Function.Injective f := fun i k h ↦
    hcol i k (f i) (hf i) (h ▸ hf k)
  exact ⟨⟨f, hinj⟩, hf, fun i j hij ↦ hrow i (f i) j (hf i) hij⟩

/-- Every profile with more workers than firms has a stable injection at nonnegative cost.
This uses the existing convention that an unmatched worker accepts any firm. -/
theorem exists_isStable {n w : ℕ} (p : Profile n w) (hcard : n < w)
    {ε : ℝ} (hε : 0 ≤ ε) : ∃ m : Matching n w, IsStable p ε m := by
  obtain ⟨A, B, hB, hA⟩ := fixed_offers p
  obtain ⟨m, hm, hrow⟩ := matching_of_fixed_offers p A B hB hA hcard
  refine ⟨m, ?_⟩
  intro i j hblock
  have hF : firmKey p i (m i) < firmKey p i j :=
    Prod.Lex.toLex_lt_toLex.mpr (Or.inl
      ((le_add_of_nonneg_right hε).trans_lt hblock.2.1))
  have hnotF : (i, m i) ∉ rejectF p A := by
    simpa only [hB, mem_compl_iff] using (hm i).2
  have hij : (i, j) ∉ A := fun h ↦ hnotF ⟨(hm i).1, j, h, hF⟩
  have hijB : (i, j) ∈ B := by
    have hrej : (i, j) ∈ rejectW p B := by
      simpa only [hA, mem_compl_iff, not_not] using hij
    exact hrej.1
  obtain ⟨k, hk, hmax⟩ := Set.exists_max_image {k | (k, j) ∈ B}
    (fun k ↦ workerKey p k j) (Set.toFinite _) ⟨i, hijB⟩
  have hkA : (k, j) ∈ A := by
    rw [hA]
    exact fun h ↦ (not_lt_of_ge (hmax h.2.choose h.2.choose_spec.1)) h.2.choose_spec.2
  have hkj : m k = j := hrow k j ⟨hkA, hk⟩
  apply (not_lt_of_ge (hmax i hijB))
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl
    ((le_add_of_nonneg_right hε).trans_lt (hblock.2.2 k hkj)))

end WorkerCompromiseProof.Imbalanced
