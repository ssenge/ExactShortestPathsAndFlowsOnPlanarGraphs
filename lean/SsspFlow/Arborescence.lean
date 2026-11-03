import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Elementary core of `notes/DMST.md`

* `reduced_nonneg_out`, `reduced_nonneg_in`, `reduced_le`, `tight`: Lemma 1, the new weight of an arc into the contracted set.
* `lower_step`, `removed_ge`: the arithmetic of Lemma 3.
* `upper_step`: the arithmetic of Lemma 2.
* `halving`: the count of Lemma 4, for a function without fixed points.

Not here: that the unpacked set is an arborescence, the contraction on graphs, and all round bounds.
-/

namespace SsspFlow.Arborescence

/-- An arc into `A` from outside the component: `β` is the least entering value. -/
theorem reduced_nonneg_out {w dv β : ℤ} (h : β ≤ w + dv) : 0 ≤ w + dv - β := by
  linarith

/-- An arc into `A` from the component but outside `A`: the tail is farther than `β`, and the triangle inequality holds. -/
theorem reduced_nonneg_in {w dv dx β : ℤ} (htri : dx ≤ w + dv) (hfar : β < dx) : 0 ≤ w + dv - β := by
  linarith

/-- The weight of an arc into `A` does not grow, since the head has distance at most `β`. -/
theorem reduced_le {w dv β : ℤ} (hA : dv ≤ β) : w + dv - β ≤ w := by
  linarith

/-- The arc that attains `β` has weight zero. -/
theorem tight {w dv β : ℤ} (h : β = w + dv) : w + dv - β = 0 := by
  linarith

/-- **Lemma 2**, arithmetic: the unpacked tree costs the arc in, the path, and the rest, which is the new weight plus `β`. -/
theorem upper_step {wxy dy rest β : ℤ} : (wxy + dy) + rest = ((wxy + dy - β) + rest) + β := by
  ring

/-- **Lemma 3**, arithmetic. `removed` is the weight of the in-arcs of `A` that the contraction drops, and it is at least `dy`.
Then the new tree costs at most the old tree minus `β`. -/
theorem lower_step {wT wxy dy removed rest β : ℤ} (hT : wT = wxy + removed + rest) (hrem : dy ≤ removed) :
    (wxy + dy - β) + rest ≤ wT - β := by
  linarith

/-- **Lemma 3**, the bound on `removed`, when the path from `y` re-enters `A` by an arc of value at least `β` and `dy ≤ β`. -/
theorem removed_ge {wre dre rest dy β : ℤ} (hre : β ≤ wre + dre) (hA : dy ≤ β) (hrest : dre ≤ rest) : dy ≤ wre + rest := by
  linarith

/-- **Lemma 4**, the count. If every class holds a point together with its image under a function without fixed points, then
every class has at least two points, so there are at most half as many classes as points. -/
theorem halving {α β : Type*} [Fintype α] [Fintype β] (cls : α → β) (hsurj : Function.Surjective cls)
    (f : α → α) (hf : ∀ a, f a ≠ a) (hcls : ∀ a, cls (f a) = cls a) : 2 * Fintype.card β ≤ Fintype.card α := by
  classical
  have h : ∀ b : β, 2 ≤ (Finset.univ.filter fun a => cls a = b).card := by
    intro b
    obtain ⟨a, rfl⟩ := hsurj b
    have : ({a, f a} : Finset α) ⊆ Finset.univ.filter fun x => cls x = cls a := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · simp
      · simp [hcls]
    calc 2 = ({a, f a} : Finset α).card := (Finset.card_pair (hf a).symm).symm
      _ ≤ _ := Finset.card_le_card this
  have hsum : ∑ b : β, (Finset.univ.filter fun a => cls a = b).card = Fintype.card α := by
    have := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset α)) (t := (Finset.univ : Finset β)) (f := cls)
      (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
    simpa using this.symm
  calc 2 * Fintype.card β = ∑ _b : β, 2 := by simp [mul_comm]
    _ ≤ ∑ b : β, (Finset.univ.filter fun a => cls a = b).card := Finset.sum_le_sum fun b _ => h b
    _ = Fintype.card α := hsum

end SsspFlow.Arborescence
