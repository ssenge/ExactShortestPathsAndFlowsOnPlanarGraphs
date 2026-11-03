import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Elementary core of `notes/REPLACEMENT.md`

* `crossing`: a walk from a position at most `i` to a position above `i` has a step that crosses `i`. This is the point of Lemma 1.
* `no_forward_use`, `no_backward_use`: the two cases of Lemma 3 on undirected networks.
* `reduced_telescope`: reduced weights along a walk differ from weights by the potentials at its ends.

Not here: graphs, the labels and all round bounds.
-/

namespace SsspFlow.Replacement

/-- **Lemma 1**, the crossing step. Reversed arcs only lower the position, so the step found here is an arc of the graph. -/
theorem crossing {α : Type*} (pos : α → ℕ) (i : ℕ) :
    ∀ (x : α) (l : List α) (y : α), pos x ≤ i → i < pos y →
      ∃ a b, List.IsInfix [a, b] (x :: l ++ [y]) ∧ pos a ≤ i ∧ i < pos b := by
  intro x l
  induction l generalizing x with
  | nil =>
    intro y hx hy
    exact ⟨x, y, ⟨[], [], by simp⟩, hx, hy⟩
  | cons z l ih =>
    intro y hx hy
    by_cases hz : pos z ≤ i
    · obtain ⟨a, b, ⟨s, t, h⟩, ha, hb⟩ := ih z y hz hy
      refine ⟨a, b, ⟨x :: s, t, ?_⟩, ha, hb⟩
      simpa using h
    · refine ⟨x, z, ⟨[], l ++ [y], by simp⟩, hx, by omega⟩

/-- **Lemma 3**, first case. If `v` lies behind the arc as seen from `s`, then a walk from `v` through `vi` and then the arc to
`vj` costs more than going from `v` to `vj` directly. -/
theorem no_forward_use {d_v_vj d_vj_t w d_v_vi d_v_t : ℤ} (hw : 0 < w) (hbehind : d_v_vi = w + d_v_vj)
    (htri : d_v_t ≤ d_v_vj + d_vj_t) : d_v_t < d_v_vi + w + d_vj_t := by
  linarith

/-- **Lemma 3**, second case. Using the arc against the direction of `P` contradicts that `P` is shortest. -/
theorem no_backward_use {d_vi_t d_vj_t w : ℤ} (hw : 0 < w) (hP : d_vi_t = w + d_vj_t) : ¬ d_vj_t = w + d_vi_t := by
  intro h
  linarith

/-- Reduced weights along a walk: the sum of `w + φ a - φ b` over consecutive pairs is the sum of `w` plus `φ x - φ y`. -/
theorem reduced_telescope {α : Type*} (w : α → α → ℤ) (φ : α → ℤ) :
    ∀ (x : α) (l : List α),
      ((x :: l).zip l).foldr (fun p r => w p.1 p.2 + φ p.1 - φ p.2 + r) 0 =
        ((x :: l).zip l).foldr (fun p r => w p.1 p.2 + r) 0 + φ x - φ ((x :: l).getLast (by simp)) := by
  intro x l
  induction l generalizing x with
  | nil => simp
  | cons z l ih =>
    have h := ih z
    simp only [List.zip_cons_cons, List.foldr_cons] at h ⊢
    rw [h]
    simp only [List.getLast_cons_cons]
    ring

end SsspFlow.Replacement
