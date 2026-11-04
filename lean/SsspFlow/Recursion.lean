import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic.IntervalCases

/-!
# The repaired recursion of `notes/RECURSION.md`

An index model of the recursion ShortestCycle of [18, Alg. 3] with the repair of Lemma S.

The faces of the dual path `P` are indexed by `0, …, m`, and `lam t` is the length `λ_t` of a
shortest walk in the level-one annulus between the two copies of the face `p_t`. A node of the
recursion is an annulus with an index range `[j, k]`. In a leaf, `k ≤ j + 1`, and the leaf computes
the paths of `j` and `k`. In any other annulus the recursion computes the path `P_i` of one index
`i` of its range, with `i1 ≤ i ≤ i2` the least and the greatest index of a copy of `P` on it, and it
drops every index strictly between `i1` and `i2`. Each side then either has an overlap, in which
case the overlap rule computes every index between the end of the range and `i`, or is called
as a child annulus with the range `[j, i1]` or `[i2, k]`, or has an empty range and is not called
((O2) of Lemma O: a side without overlap and with a nonempty range is one subgraph and gets the
call). The repair adds the two indices `max i1 j` and `min i2 k` to every annulus that is not a
leaf.

Two facts of the note enter as hypotheses, and nothing else does.
* The conclusion of Lemma S1, the Witness Interval Lemma, is the field `dom` of a node: for every
  dropped index `t`, either every `q` in `[i1, t]` or every `q` in `[t, i2]` has `lam q ≤ lam t`.
* (INV) and (C23) of Lemma O: every computed length is `lam t` for the index `t` it is computed
  for. So a computed set of indices stands for the computed lengths, and (O3) is not needed.

`Rec.exact` is the completeness half of Lemma S2: if `Λ` is a lower bound of `lam` and some index
of the range attains it, then a computed index attains it. `Rec.sound` is the other half, and
`Rec.isLeast` combines them: the least computed length is `Λ`. `Rec.computed_subset` shows that an
annulus computes only indices of its range. `computed0` is the recursion without the repair, and
`miss` shows on the index pattern of the eleven-vertex instance of the note that it can miss the
minimum, whatever happens on the side that does not contain it; `repair_hits` is the repaired
recursion on the same tree.

Not here: the proof of Lemma S1, the graphs and their walks, the sides of an incision, the
topology, and all round bounds.
-/

namespace SsspFlow.Recursion

mutual
/-- An annulus of the recursion with the index range `[j, k]`. -/
inductive Rec (lam : ℕ → ℕ) : ℕ → ℕ → Type
  /-- A leaf has at most two indices and computes both. -/
  | leaf {j k : ℕ} (hjk : j ≤ k) (hk : k ≤ j + 1) : Rec lam j k
  /-- An annulus that computes `P_i`, with `i1 ≤ i ≤ i2` the extreme indices of the copies of `P`
  on it, the conclusion of Lemma S1 for every dropped index, and its two sides. -/
  | node {j k : ℕ} (i i1 i2 : ℕ) (hji : j ≤ i) (hik : i ≤ k) (h1 : i1 ≤ i) (h2 : i ≤ i2)
      (dom : ∀ t, i1 < t → t < i2 →
        (∀ q, i1 ≤ q → q ≤ t → lam q ≤ lam t) ∨ (∀ q, t ≤ q → q ≤ i2 → lam q ≤ lam t))
      (left : Side lam j i1) (right : Side lam i2 k) : Rec lam j k
/-- One side of an incision, with the range `[lo, hi]` it would get as a child. -/
inductive Side (lam : ℕ → ℕ) : ℕ → ℕ → Type
  /-- The path `P_i` meets the bounding path of this side: the overlap rule applies, and the side is
  not called. -/
  | overlap {lo hi : ℕ} : Side lam lo hi
  /-- The side is called with the range `[lo, hi]`. -/
  | child {lo hi : ℕ} (r : Rec lam lo hi) : Side lam lo hi
  /-- The range is empty and the side is not called. -/
  | empty {lo hi : ℕ} (h : hi < lo) : Side lam lo hi
end

variable {lam : ℕ → ℕ}

/-- The range of an annulus is not empty. -/
theorem Rec.le {j k : ℕ} : Rec lam j k → j ≤ k
  | .leaf hjk _ => hjk
  | .node _ _ _ hji hik _ _ _ _ _ => hji.trans hik

mutual
/-- The indices computed in an annulus and its subtree, with the repair. The overlap rule of the
`j`-side computes `[j, i]` and that of the `k`-side `[i, k]`. -/
def Rec.computed : ∀ {j k : ℕ}, Rec lam j k → Finset ℕ
  | j, k, .leaf _ _ => {j, k}
  | j, k, .node i i1 i2 _ _ _ _ _ left right =>
      {i, max i1 j, min i2 k} ∪ left.computed (Finset.Icc j i) ∪ right.computed (Finset.Icc i k)
/-- The indices computed on one side, given the set `ov` that the overlap rule would compute. -/
def Side.computed : ∀ {lo hi : ℕ}, Finset ℕ → Side lam lo hi → Finset ℕ
  | _, _, ov, .overlap => ov
  | _, _, _, .child r => r.computed
  | _, _, _, .empty _ => ∅
end

mutual
/-- The recursion of [18] as written: the same tree, without the two extra indices. -/
def Rec.computed0 : ∀ {j k : ℕ}, Rec lam j k → Finset ℕ
  | j, k, .leaf _ _ => {j, k}
  | j, k, .node i _ _ _ _ _ _ _ left right =>
      {i} ∪ left.computed0 (Finset.Icc j i) ∪ right.computed0 (Finset.Icc i k)
/-- The indices computed on one side without the repair. -/
def Side.computed0 : ∀ {lo hi : ℕ}, Finset ℕ → Side lam lo hi → Finset ℕ
  | _, _, ov, .overlap => ov
  | _, _, _, .child r => r.computed0
  | _, _, _, .empty _ => ∅
end

mutual
/-- An annulus computes only indices of its range. -/
theorem Rec.computed_subset : ∀ {j k : ℕ} (r : Rec lam j k), r.computed ⊆ Finset.Icc j k
  | j, k, .leaf hjk hk => by
      intro s hs
      simp only [Rec.computed, Finset.mem_insert, Finset.mem_singleton] at hs
      rw [Finset.mem_Icc]
      omega
  | j, k, .node i i1 i2 hji hik h1 h2 _ left right => by
      have hl := Side.computed_subset left (Finset.Icc j i) (Finset.Icc_subset_Icc le_rfl hik)
        le_rfl (h1.trans hik)
      have hr := Side.computed_subset right (Finset.Icc i k) (Finset.Icc_subset_Icc hji le_rfl)
        (hji.trans h2) le_rfl
      intro s hs
      simp only [Rec.computed, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with ((rfl | rfl | rfl) | hs) | hs
      · exact Finset.mem_Icc.2 ⟨hji, hik⟩
      · exact Finset.mem_Icc.2 ⟨le_max_right _ _, max_le (h1.trans hik) (hji.trans hik)⟩
      · exact Finset.mem_Icc.2 ⟨le_min (hji.trans h2) (hji.trans hik), min_le_right _ _⟩
      · exact hl hs
      · exact hr hs
/-- One side computes only indices of the enclosing range. -/
theorem Side.computed_subset : ∀ {lo hi : ℕ} (s : Side lam lo hi) (ov : Finset ℕ) {a b : ℕ},
    ov ⊆ Finset.Icc a b → a ≤ lo → hi ≤ b → s.computed ov ⊆ Finset.Icc a b
  | _, _, .overlap, ov, a, b, hov, _, _ => by
      simpa only [Side.computed] using hov
  | _, _, .child r, ov, a, b, _, hlo, hhi => by
      simp only [Side.computed]
      exact r.computed_subset.trans (Finset.Icc_subset_Icc hlo hhi)
  | _, _, .empty _, ov, a, b, _, _, _ => by
      simp [Side.computed]
end

mutual
/-- Without the repair, nothing more is computed. -/
theorem Rec.computed0_subset : ∀ {j k : ℕ} (r : Rec lam j k), r.computed0 ⊆ r.computed
  | j, k, .leaf hjk hk => by
      simp only [Rec.computed0, Rec.computed]
      exact le_rfl
  | j, k, .node i i1 i2 hji hik h1 h2 _ left right => by
      have hl := Side.computed0_subset left (Finset.Icc j i)
      have hr := Side.computed0_subset right (Finset.Icc i k)
      intro s hs
      simp only [Rec.computed0, Finset.mem_union, Finset.mem_singleton] at hs
      simp only [Rec.computed, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      rcases hs with (rfl | hs) | hs
      · exact Or.inl (Or.inl (Or.inl rfl))
      · exact Or.inl (Or.inr (hl hs))
      · exact Or.inr (hr hs)
/-- Without the repair, nothing more is computed on a side. -/
theorem Side.computed0_subset : ∀ {lo hi : ℕ} (s : Side lam lo hi) (ov : Finset ℕ),
    s.computed0 ov ⊆ s.computed ov
  | _, _, .overlap, ov => by
      simp only [Side.computed0, Side.computed]
      exact le_rfl
  | _, _, .child r, ov => by
      simp only [Side.computed0, Side.computed]
      exact r.computed0_subset
  | _, _, .empty _, ov => by
      simp [Side.computed0]
end

section Exact

variable {Λ : ℕ}

mutual
/-- **Lemma S2**, completeness. If `Λ` is a lower bound of `lam` and an index of the range attains
it, then a computed index attains it. The proof is the case analysis of the note: a dropped index
`t` passes to `max i1 j` or to `min i2 k` by Lemma S1, since both lie in the range and in the
witness interval; an index at or below `i1` passes to the `j`-side, and one at or above `i2` to the
`k`-side. -/
theorem Rec.exact (hΛ : ∀ q, Λ ≤ lam q) : ∀ {j k : ℕ} (r : Rec lam j k) (t : ℕ),
    j ≤ t → t ≤ k → lam t = Λ → ∃ s ∈ r.computed, lam s = Λ
  | j, k, .leaf hjk hk, t, hjt, htk, ht => by
      refine ⟨t, ?_, ht⟩
      simp only [Rec.computed, Finset.mem_insert, Finset.mem_singleton]
      omega
  | j, k, .node i i1 i2 hji hik h1 h2 dom left right, t, hjt, htk, ht => by
      rcases Nat.lt_or_ge i1 t with h1t | ht1
      swap
      · -- `t ≤ i1`: the `j`-side holds `t` in its range `[j, i1]`.
        obtain ⟨s, hs, hsl⟩ := Side.exact hΛ left (Finset.Icc j i)
          (Finset.Icc_subset_Icc le_rfl h1) t hjt ht1 ht
        exact ⟨s, by simp only [Rec.computed, Finset.mem_union]; exact Or.inl (Or.inr hs), hsl⟩
      rcases Nat.lt_or_ge t i2 with ht2 | h2t
      swap
      · -- `i2 ≤ t`: the `k`-side holds `t` in its range `[i2, k]`.
        obtain ⟨s, hs, hsl⟩ := Side.exact hΛ right (Finset.Icc i k)
          (Finset.Icc_subset_Icc h2 le_rfl) t h2t htk ht
        exact ⟨s, by simp only [Rec.computed, Finset.mem_union]; exact Or.inr hs, hsl⟩
      -- `i1 < t < i2`: `t` is dropped, and Lemma S1 gives a witness interval.
      rcases dom t h1t ht2 with hlow | hhigh
      · refine ⟨max i1 j, ?_, ?_⟩
        · simp [Rec.computed]
        · have h := hlow (max i1 j) (le_max_left _ _) (max_le h1t.le hjt)
          have h' := hΛ (max i1 j)
          omega
      · refine ⟨min i2 k, ?_, ?_⟩
        · simp [Rec.computed]
        · have h := hhigh (min i2 k) (le_min ht2.le htk) (min_le_left _ _)
          have h' := hΛ (min i2 k)
          omega
/-- Completeness on one side. An overlap computes the whole range, a child continues by
induction, and an empty range holds no index. -/
theorem Side.exact (hΛ : ∀ q, Λ ≤ lam q) : ∀ {lo hi : ℕ} (s : Side lam lo hi) (ov : Finset ℕ),
    Finset.Icc lo hi ⊆ ov → ∀ t : ℕ, lo ≤ t → t ≤ hi → lam t = Λ →
      ∃ s' ∈ s.computed ov, lam s' = Λ
  | _, _, .overlap, ov, hov, t, hlt, hth, ht => by
      refine ⟨t, ?_, ht⟩
      simp only [Side.computed]
      exact hov (Finset.mem_Icc.2 ⟨hlt, hth⟩)
  | _, _, .child r, ov, _, t, hlt, hth, ht => by
      simp only [Side.computed]
      exact r.exact hΛ t hlt hth ht
  | _, _, .empty h, ov, _, t, hlt, hth, _ => by
      omega
end

/-- **Lemma S2**, soundness. Every computed length is at least `Λ`. -/
theorem Rec.sound (hΛ : ∀ q, Λ ≤ lam q) {j k : ℕ} (r : Rec lam j k) :
    ∀ s ∈ r.computed, Λ ≤ lam s :=
  fun s _ => hΛ s

/-- **Lemma S2.** With the repair, the least computed length is the minimum `Λ`, whenever some
index of the range attains it. For the level-one annulus the range is `[0, m]`, so `Λ` is the
minimum of `lam` over all indices of `P`. -/
theorem Rec.isLeast (hΛ : ∀ q, Λ ≤ lam q) {j k : ℕ} (r : Rec lam j k) {t : ℕ}
    (hjt : j ≤ t) (htk : t ≤ k) (ht : lam t = Λ) :
    IsLeast (lam '' (r.computed : Set ℕ)) Λ := by
  obtain ⟨s, hs, hsl⟩ := r.exact hΛ t hjt htk ht
  refine ⟨⟨s, Finset.mem_coe.2 hs, hsl⟩, ?_⟩
  rintro v ⟨s, _, rfl⟩
  exact hΛ s

end Exact

section Instance

/-- The lengths of the eleven-vertex instance of the note as the recursion sees them:
`λ_4 = λ_5 = 15` for the minimum cut, `λ_6 = 37` for the reported value, and `99` for the
indices that do not matter (there, the lengths are at least 99). -/
def lamEx : ℕ → ℕ := fun t => if t = 4 ∨ t = 5 then 15 else if t = 6 then 37 else 99

theorem lamEx_lower (q : ℕ) : 15 ≤ lamEx q := by
  unfold lamEx
  split_ifs <;> omega

theorem lamEx_five : lamEx 5 = 15 := by
  simp [lamEx]

/-- Level two, the annulus with range `[5, 7]` of the note: `P_6` has copies of `p_4` to `p_7`, so
`i1 = 4` lies below the range, the `j`-side is empty, and index 5 is dropped on the strength of
`P_4`, which level one dropped already. -/
def exRight : Rec lamEx 5 7 :=
  .node 6 4 7 (by omega) (by omega) (by omega) (by omega)
    (by
      intro t h1 h2
      interval_cases t
      · left; intro q hq1 hq2; interval_cases q <;> decide
      · left; intro q hq1 hq2; interval_cases q <;> decide)
    (.empty (by omega))
    (.child (.leaf le_rfl (by omega)))

/-- Level one, range `[0, 7]`: `P_3` has copies of `p_3` to `p_5`, so index 4 is dropped on the
strength of `P_5`. The `j`-side, with range `[0, 3]`, is arbitrary. -/
def exRoot (left : Side lamEx 0 3) : Rec lamEx 0 7 :=
  .node 3 3 5 (by omega) (by omega) (by omega) (by omega)
    (by
      intro t h1 h2
      interval_cases t
      right; intro q hq1 hq2; interval_cases q <;> decide)
    left
    (.child exRight)

/-- **The defect.** Without the repair, no computed length of this tree is the minimum 15,
whatever the `j`-side of the root computes. -/
theorem miss (left : Side lamEx 0 3) : ∀ s ∈ (exRoot left).computed0, lamEx s ≠ 15 := by
  intro s hs
  have hl : left.computed0 (Finset.Icc 0 3) ⊆ Finset.Icc 0 3 :=
    (Side.computed0_subset left _).trans
      (Side.computed_subset left _ (Finset.Subset.refl _) le_rfl le_rfl)
  simp only [exRoot, exRight, Rec.computed0, Side.computed0, Finset.mem_union,
    Finset.mem_insert, Finset.mem_singleton, Finset.union_empty, or_self] at hs
  rcases hs with (rfl | hs) | (rfl | rfl)
  · decide
  · have := Finset.mem_Icc.1 (hl hs)
    unfold lamEx
    split_ifs <;> omega
  · decide
  · decide

/-- **The repair** on the same tree computes the minimum: index 5 is `max i1 j` of level two. -/
theorem repair_hits (left : Side lamEx 0 3) : ∃ s ∈ (exRoot left).computed, lamEx s = 15 :=
  (exRoot left).exact lamEx_lower 5 (by omega) (by omega) lamEx_five

end Instance

end SsspFlow.Recursion
