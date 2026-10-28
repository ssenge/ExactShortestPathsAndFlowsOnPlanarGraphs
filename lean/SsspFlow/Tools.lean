import SsspFlow.LemmaD
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Tools of the repair of [1, Lemmas 15 and 16]: gluing, rounding, parameters

Lemmas R1 and R6 and the parameter choice of `notes/LEMMA15.md` (§4, §7), stated for walks in a
multidigraph whose arcs from `a` to `b` form the type `E a b` (`FaceDisjoint.Walk`, real
lengths). Distances are infima over walks, so "for every walk on one side there is a walk on
the other side that is at most `λ` times as long" is the walk form of `dist ≤ λ · dist`.

* `glue` (Lemma R1, combinatorial core). In a glued graph every arc belongs to one piece, and
  every vertex that is not a terminal image has all its arcs in one piece. Then every walk
  between terminal images cuts into segments of a single piece with no terminal image inside
  (`decomp`). If each such segment is matched on the other side by a walk at most `λ` times as
  long, so is every walk between terminal images. The quotient construction `Glue(A; ~)` is not
  formalized: the hypotheses `hloc` and `hseg` are what it provides, with `hseg` coming from
  `dist_{B_i} ≤ λ · dist_{A_i}` on the terminals of piece `i`.
* `rounding` (Lemma R6). Cap every length at `m` and round it up to a multiple of `η`. If
  `η · |N| ≤ ε` and the terminal distance `d(s, t)` lies in `[1, m]`, the new distance is in
  `[d(s, t), (1 + ε) · d(s, t)]`. `rnd_bounds` gives the range of the new lengths.
* `level_step`: the error of one level of Lemma 15′ (oracle, LP and rounding, one factor
  `1 + ε'` each), so `(1 + ε')^(3h)` at height `h`.
* `params`: `ε' = ε / (2(3H + 1))` gives `(1 + ε')^(3H + 1) ≤ 1 + ε` for `ε ∈ [0, 1]`.

## Not formalized
The planarity statements (Lemmas R3, R5, R7, Lemma 14′), the Monge condition, the realization
of [10], and the distributed algorithm.
-/

namespace SsspFlow.Tools

open SsspFlow.FaceDisjoint

universe u

variable {N : Type u} {E : N → N → Type u}

namespace Walk

open FaceDisjoint.Walk

lemma wt_mono (ℓ ℓ' : ∀ a b, E a b → ℝ) (h : ∀ a b e, ℓ a b e ≤ ℓ' a b e) :
    ∀ {a b : N} (p : FaceDisjoint.Walk E a b), p.wt ℓ ≤ p.wt ℓ'
  | _, _, .nil _ => le_rfl
  | _, _, .cons e p => by simp only [wt_cons]; linarith [h _ _ e, wt_mono ℓ ℓ' h p]

lemma wt_le_add_len (ℓ ℓ' : ∀ a b, E a b → ℝ) (η : ℝ) (h : ∀ a b e, ℓ' a b e ≤ ℓ a b e + η) :
    ∀ {a b : N} (p : FaceDisjoint.Walk E a b), p.wt ℓ' ≤ p.wt ℓ + η * p.len
  | _, _, .nil _ => by simp
  | _, _, .cons e p => by
    simp only [wt_cons, len_cons]; push_cast; linarith [h _ _ e, wt_le_add_len ℓ ℓ' η h p]

lemma wt_nonneg (ℓ : ∀ a b, E a b → ℝ) (h : ∀ a b e, 0 ≤ ℓ a b e) :
    ∀ {a b : N} (p : FaceDisjoint.Walk E a b), 0 ≤ p.wt ℓ
  | _, _, .nil _ => le_rfl
  | _, _, .cons e p => by simp only [wt_cons]; linarith [h _ _ e, wt_nonneg ℓ h p]

end Walk

/-! ## Lemma R1: gluing -/

section Glue

variable {I : Type u} (piece : ∀ a b, E a b → I) (term : N → Prop)

/-- `Seg i p`: every arc of `p` lies in piece `i`, `p` has an arc, and no interior vertex of `p`
is a terminal image. -/
inductive Seg (i : I) : {a b : N} → FaceDisjoint.Walk E a b → Prop
  | one {a b : N} (e : E a b) : piece a b e = i → Seg i (.cons e (.nil b))
  | cons {a b c : N} (e : E a b) (p : FaceDisjoint.Walk E b c) :
      piece a b e = i → ¬ term b → Seg i p → Seg i (.cons e p)

variable {piece term}

lemma Seg.head {i : I} {a b c : N} {e : E a b} {p : FaceDisjoint.Walk E b c}
    (h : Seg piece term i (.cons e p)) : piece a b e = i := by
  cases h <;> assumption

/-- Cut a walk that ends at a terminal image after its first segment. -/
lemma decomp (ℓ : ∀ a b, E a b → ℝ)
    (hloc : ∀ v, ¬ term v → ∃ i, (∀ a (e : E a v), piece a v e = i) ∧
      (∀ b (e : E v b), piece v b e = i)) :
    ∀ {a b : N} (p : FaceDisjoint.Walk E a b), term b → 0 < p.len →
      ∃ (t : N) (i : I) (s : FaceDisjoint.Walk E a t) (r : FaceDisjoint.Walk E t b),
        term t ∧ Seg piece term i s ∧ r.len < p.len ∧ p.wt ℓ = s.wt ℓ + r.wt ℓ
  | _, _, .nil _, _, h => by simp at h
  | a, b, .cons (b := c) e p, hb, _ => by
    by_cases hc : term c
    · exact ⟨c, piece a c e, .cons e (.nil c), p, hc, .one e rfl, by simp, by simp⟩
    · cases p with
      | nil => exact absurd hb hc
      | cons e' p' =>
        obtain ⟨t, i, s, r, ht, hs, hr, hw⟩ := decomp ℓ hloc (.cons e' p') hb (by simp)
        obtain ⟨j, hin, hout⟩ := hloc c hc
        cases s with
        | nil => cases hs
        | cons e₁ s₁ =>
          have hi : i = j := hs.head.symm.trans (hout _ e₁)
          refine ⟨t, i, .cons e (.cons e₁ s₁), r, ht, .cons e _ ((hin a e).trans hi.symm) hc hs,
            by simp at hr ⊢; omega, ?_⟩
          simp only [FaceDisjoint.Walk.wt_cons] at hw ⊢
          linarith

variable {N' : Type u} {E' : N' → N' → Type u} {T : Type u}

/-- **Lemma R1**, walk form. `ιA` and `ιB` place the terminal classes `T` in the two glued
graphs; `term` marks the terminal images of the first one. -/
theorem glue (ℓ : ∀ a b, E a b → ℝ) (ℓ' : ∀ a b, E' a b → ℝ) (lam : ℝ)
    (hloc : ∀ v, ¬ term v → ∃ i, (∀ a (e : E a v), piece a v e = i) ∧
      (∀ b (e : E v b), piece v b e = i))
    (ιA : T → N) (ιB : T → N') (hinj : Function.Injective ιA) (hterm : ∀ v, term v ↔ ∃ x, ιA x = v)
    (hseg : ∀ i x y (s : FaceDisjoint.Walk E (ιA x) (ιA y)), Seg piece term i s →
      ∃ q : FaceDisjoint.Walk E' (ιB x) (ιB y), q.wt ℓ' ≤ lam * s.wt ℓ)
    (x y : T) (p : FaceDisjoint.Walk E (ιA x) (ιA y)) :
    ∃ q : FaceDisjoint.Walk E' (ιB x) (ιB y), q.wt ℓ' ≤ lam * p.wt ℓ := by
  suffices H : ∀ n {a b : N} (p : FaceDisjoint.Walk E a b), p.len = n → ∀ x y, ιA x = a →
      ιA y = b → ∃ q : FaceDisjoint.Walk E' (ιB x) (ιB y), q.wt ℓ' ≤ lam * p.wt ℓ by
    exact H _ p rfl x y rfl rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b p hn x y hx hy
  cases p with
  | nil =>
    obtain rfl := hinj (hx.trans hy.symm)
    exact ⟨.nil _, by simp⟩
  | cons e p' =>
    obtain ⟨t, i, s, r, ht, hs, hr, hw⟩ :=
      decomp ℓ hloc (.cons e p') ((hterm b).2 ⟨y, hy⟩) (by simp)
    obtain ⟨z, rfl⟩ := (hterm t).1 ht
    subst hx hy
    obtain ⟨q₁, h₁⟩ := hseg i x z s hs
    obtain ⟨q₂, h₂⟩ := ih r.len (hn ▸ hr) r rfl z y rfl rfl
    refine ⟨q₁.append q₂, ?_⟩
    rw [FaceDisjoint.Walk.wt_append, hw, mul_add]
    linarith

end Glue

/-! ## Lemma R6: rounding -/

/-- Lengths capped at `m` and rounded up to a multiple of `η`. -/
noncomputable def rnd (η m : ℝ) (ℓ : ∀ a b, E a b → ℝ) : ∀ a b, E a b → ℝ :=
  fun a b e => η * ⌈min (ℓ a b e) m / η⌉

lemma rnd_bounds {η : ℝ} (hη : 0 < η) (m : ℝ) (ℓ : ∀ a b, E a b → ℝ) (a b : N) (e : E a b) :
    (∃ k : ℤ, rnd η m ℓ a b e = η * k) ∧
      min (ℓ a b e) m ≤ rnd η m ℓ a b e ∧ rnd η m ℓ a b e < min (ℓ a b e) m + η := by
  refine ⟨⟨_, rfl⟩, ?_, ?_⟩
  · have := Int.le_ceil (min (ℓ a b e) m / η)
    calc min (ℓ a b e) m = η * (min (ℓ a b e) m / η) := by field_simp
      _ ≤ rnd η m ℓ a b e := mul_le_mul_of_nonneg_left this hη.le
  · have := Int.ceil_lt_add_one (min (ℓ a b e) m / η)
    calc rnd η m ℓ a b e < η * (min (ℓ a b e) m / η + 1) := mul_lt_mul_of_pos_left this hη
      _ = min (ℓ a b e) m + η := by field_simp

lemma min_le_wt_rnd {η m : ℝ} (hη : 0 < η) (hm : 0 ≤ m) (ℓ : ∀ a b, E a b → ℝ)
    (h0 : ∀ a b e, 0 ≤ ℓ a b e) :
    ∀ {a b : N} (p : FaceDisjoint.Walk E a b), min (p.wt ℓ) m ≤ p.wt (rnd η m ℓ)
  | _, _, .nil _ => by simp [hm]
  | _, _, .cons e p => by
    have he := (rnd_bounds hη m ℓ _ _ e).2.1
    have hp := min_le_wt_rnd hη hm ℓ h0 p
    have := Walk.wt_nonneg ℓ h0 p
    simp only [FaceDisjoint.Walk.wt_cons]
    rcases le_total (ℓ _ _ e) m with h1 | h1 <;> rcases le_total (p.wt ℓ) m with h2 | h2 <;>
      simp only [min_eq_left, min_eq_right, h1, h2] at he hp <;>
      first
      | exact (min_le_left _ _).trans (by linarith)
      | exact (min_le_right _ _).trans (by linarith [h0 _ _ e])

/-- **Lemma R6**, walk form: rounding never shortens a walk between `s` and `t`, and some walk
gets at most `1 + ε` times longer than any given one. -/
theorem rounding [Fintype N] (ℓ : ∀ a b, E a b → ℝ) (h0 : ∀ a b e, 0 ≤ ℓ a b e) {η m ε : ℝ}
    (hη : 0 < η) (hε : η * Fintype.card N ≤ ε) {s t : N}
    (hm : ∃ q : FaceDisjoint.Walk E s t, q.wt ℓ ≤ m)
    (h1 : ∀ p : FaceDisjoint.Walk E s t, 1 ≤ p.wt ℓ) :
    (∀ p : FaceDisjoint.Walk E s t, ∃ q : FaceDisjoint.Walk E s t, q.wt ℓ ≤ p.wt (rnd η m ℓ)) ∧
      (∀ p : FaceDisjoint.Walk E s t,
        ∃ q : FaceDisjoint.Walk E s t, q.wt (rnd η m ℓ) ≤ (1 + ε) * p.wt ℓ) := by
  obtain ⟨q₀, hq₀⟩ := hm
  have hm0 : 0 ≤ m := (Walk.wt_nonneg ℓ h0 q₀).trans hq₀
  refine ⟨fun p => ?_, fun p => ?_⟩
  · have := min_le_wt_rnd hη hm0 ℓ h0 p
    rcases le_total (p.wt ℓ) m with h | h
    · exact ⟨p, by rwa [min_eq_left h] at this⟩
    · exact ⟨q₀, by rw [min_eq_right h] at this; linarith⟩
  · obtain ⟨q, hlen, hw⟩ := FaceDisjoint.Walk.short ℓ
      (fun y c => Walk.wt_nonneg ℓ h0 c) _ p rfl
    refine ⟨q, ?_⟩
    have hup := Walk.wt_le_add_len ℓ (rnd η m ℓ) η
      (fun a b e => (rnd_bounds hη m ℓ a b e).2.2.le.trans (by linarith [min_le_left (ℓ a b e) m]))
      q
    have hcard : η * q.len ≤ ε := (mul_le_mul_of_nonneg_left (by exact_mod_cast hlen.le) hη.le).trans hε
    have hε0 : 0 ≤ ε := (mul_nonneg hη.le (Nat.cast_nonneg _)).trans hε
    nlinarith [h1 p]

/-! ## The error per level and the parameters -/

/-- One level of Lemma 15′: `dist_C ≤ dist_{O'} ≤ λ dist_C` for the child (I2), the oracle
`dist_{O'} ≤ δ ≤ (1+e) dist_{O'}`, the LP `δ ≤ d ≤ (1+e) δ` (Lemma R5) and the rounding
`d ≤ d̂ ≤ (1+e) d` (Lemma R6) give `dist_C ≤ d̂ ≤ (1+e)^3 λ dist_C`. -/
theorem level_step {e lam dC dO δ d dh : ℝ} (he : 0 ≤ e)
    (h1 : dC ≤ dO) (h2 : dO ≤ lam * dC) (h3 : dO ≤ δ) (h4 : δ ≤ (1 + e) * dO)
    (h5 : δ ≤ d) (h6 : d ≤ (1 + e) * δ) (h7 : d ≤ dh) (h8 : dh ≤ (1 + e) * d) :
    dC ≤ dh ∧ dh ≤ (1 + e) ^ 3 * (lam * dC) := by
  refine ⟨by linarith, ?_⟩
  have := mul_le_mul_of_nonneg_left h6 (by linarith : (0 : ℝ) ≤ 1 + e)
  have := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ (1 + e) * (1 + e))
  have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ (1 + e) ^ 3)
  nlinarith

/-- **Parameters** (§7): `ε' = ε / (2(3H+1))` gives `(1 + ε')^(3H+1) ≤ 1 + ε`. -/
theorem params (H : ℕ) {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    (1 + ε / (2 * (3 * H + 1))) ^ (3 * H + 1) ≤ 1 + ε := by
  set n : ℕ := 3 * H + 1
  have hn : (0 : ℝ) < n := by positivity
  have hx : (n : ℝ) * (ε / (2 * n)) = ε / 2 := by field_simp
  have hcast : (2 * (3 * (H : ℝ) + 1)) = 2 * n := by simp [n]
  rw [hcast]
  calc (1 + ε / (2 * n)) ^ n ≤ Real.exp (ε / (2 * n)) ^ n :=
        pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (ε / (2 * n))]) n
    _ = Real.exp (ε / 2) := by rw [← Real.exp_nat_mul, hx]
    _ ≤ 1 / (1 - ε / 2) := Real.exp_bound_div_one_sub_of_interval (by linarith) (by linarith)
    _ ≤ 1 + ε := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith

end SsspFlow.Tools
