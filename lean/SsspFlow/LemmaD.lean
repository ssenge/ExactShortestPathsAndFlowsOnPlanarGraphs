import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Data.EReal.Basic

/-!
# Lemma D: the weighted face-disjoint graph

Setting of Lemma D in `sssp_flow/NOTES.md`. The face-disjoint graph `Ĝ` of [9, Sec. 3] has
corner nodes `inl c` (`c : C`) and star centres `inr z` (`z : Z`). Its arcs (`Setup.Arc`) are
* `E_R`: a ring of corners around each face, given by any relation `rg` whose reflexive-transitive
  closure joins exactly the corners of one face (`ring_face`, `ring_conn`);
* `E_C`: one arc per dual dart `d`, from a corner `src d` on the face `tl d` to a corner `dst d`
  on the face `hd d` (`src_face`, `dst_face`), the 1-1 map of [9, Prop. 5];
* `E_S`: spokes between star centres and corners, in both directions.

Lemma D weights `E_R` arcs `0`, the arc of dual dart `d` by `lam d` (any sign), and spokes by `M`.
Parallel arcs and loops are allowed. With `-Λ ≤ lam d` and `|Ĝ|·Λ < M`:
* `negCycle_iff`: `Ĝ` has a negative closed walk iff the dual `G*` has one;
* `walks`: if `G*` has no negative closed walk, every dual walk lifts to a `Ĝ` walk of equal
  weight between any corners of its end faces, and every `Ĝ` walk between corners weighs more
  than `M` or is dominated by a dual walk between their faces;
* `lemmaD`: hence, if also `|lam d| ≤ Λ` and every face has a corner, `dist_Ĝ(a, b) =
  dist_{G*}(g, h)` when the right side is finite, and `dist_Ĝ(a, b) ≥ M` otherwise.

`rotSetup` builds `Ĝ` from a combinatorial map (darts `D`, reversal `α`, face permutation `φ`):
corners are darts, faces are `φ`-orbits, the ring is `d — φ d`, and the edge `{d, α d}` gets one
`E_C` edge between `d` and `φ (α d)` for the picked dart `d` (`rot_pair`). `rot_lemmaD` is the
result for it. Planarity is not used here; it only matters for running Theorems A and B on `Ĝ`.

## Not formalized
That `Ĝ` is planar, has hop diameter `≤ 3D + 2` and simulates in `2r` rounds ([9, Props 1-3]),
and the distributed algorithms run on it.
-/

namespace SsspFlow.FaceDisjoint

universe u

/-- Walks in a multidigraph whose arcs from `a` to `b` form the type `E a b`. -/
inductive Walk {N : Type u} (E : N → N → Type u) : N → N → Type u
  | nil (a : N) : Walk E a a
  | cons {a b c : N} (e : E a b) (p : Walk E b c) : Walk E a c

namespace Walk

variable {N : Type u} {E : N → N → Type u}

def support : {a b : N} → Walk E a b → List N
  | a, _, nil _ => [a]
  | a, _, cons _ p => a :: p.support

def len : {a b : N} → Walk E a b → ℕ
  | _, _, nil _ => 0
  | _, _, cons _ p => p.len + 1

def wt (ℓ : ∀ a b, E a b → ℝ) : {a b : N} → Walk E a b → ℝ
  | _, _, nil _ => 0
  | _, _, @cons _ _ a m _ e p => ℓ a m e + p.wt ℓ

def append : {a b c : N} → Walk E a b → Walk E b c → Walk E a c
  | _, _, _, nil _, q => q
  | _, _, _, cons e p, q => cons e (p.append q)

variable (ℓ : ∀ a b, E a b → ℝ)

@[simp] lemma support_nil (a : N) : (nil a : Walk E a a).support = [a] := rfl
@[simp] lemma support_cons {a b c : N} (e : E a b) (p : Walk E b c) :
    (cons e p).support = a :: p.support := rfl
@[simp] lemma len_nil (a : N) : (nil a : Walk E a a).len = 0 := rfl
@[simp] lemma len_cons {a b c : N} (e : E a b) (p : Walk E b c) :
    (cons e p).len = p.len + 1 := rfl
@[simp] lemma wt_nil (a : N) : (nil a : Walk E a a).wt ℓ = 0 := rfl
@[simp] lemma wt_cons {a b c : N} (e : E a b) (p : Walk E b c) :
    (cons e p).wt ℓ = ℓ a b e + p.wt ℓ := rfl
@[simp] lemma nil_append {a b : N} (q : Walk E a b) : (nil a).append q = q := rfl
@[simp] lemma cons_append {a b c d : N} (e : E a b) (p : Walk E b c) (q : Walk E c d) :
    (cons e p).append q = cons e (p.append q) := rfl

@[simp] lemma wt_append : ∀ {a b c : N} (p : Walk E a b) (q : Walk E b c),
    (p.append q).wt ℓ = p.wt ℓ + q.wt ℓ
  | _, _, _, nil _, q => by simp
  | _, _, _, cons e p, q => by simp [wt_append p q, add_assoc]

@[simp] lemma len_append : ∀ {a b c : N} (p : Walk E a b) (q : Walk E b c),
    (p.append q).len = p.len + q.len
  | _, _, _, nil _, q => by simp
  | _, _, _, cons e p, q => by simp [len_append p q]; omega

lemma start_mem : ∀ {a b : N} (p : Walk E a b), a ∈ p.support
  | _, _, nil _ => by simp
  | _, _, cons _ _ => by simp

lemma length_support : ∀ {a b : N} (p : Walk E a b), p.support.length = p.len + 1
  | _, _, nil _ => rfl
  | _, _, cons _ p => by simp [length_support p]

/-- Cut a walk at a visited vertex. -/
lemma split {a b h : N} (p : Walk E a b) (hp : h ∈ p.support) :
    ∃ (p₁ : Walk E a h) (p₂ : Walk E h b), p = p₁.append p₂ := by
  induction p with
  | nil a =>
    obtain rfl : h = a := by simpa using hp
    exact ⟨nil h, nil h, rfl⟩
  | cons e p ih =>
    rcases List.mem_cons.1 hp with rfl | hp
    · exact ⟨nil h, cons e p, rfl⟩
    · obtain ⟨p₁, p₂, rfl⟩ := ih hp
      exact ⟨cons e p₁, p₂, rfl⟩

/-- A walk that repeats a vertex contains a nonempty closed subwalk. -/
lemma dup_split {a b : N} (p : Walk E a b) (hp : ¬ p.support.Nodup) :
    ∃ (y : N) (p₁ : Walk E a y) (c : Walk E y y) (p₂ : Walk E y b),
      0 < c.len ∧ p = p₁.append (c.append p₂) := by
  induction p with
  | nil a => simp at hp
  | cons e q ih =>
    rw [support_cons, List.nodup_cons, not_and_or, not_not] at hp
    rcases hp with hx | hq
    · obtain ⟨q₁, q₂, rfl⟩ := q.split hx
      exact ⟨_, nil _, cons e q₁, q₂, by simp, rfl⟩
    · obtain ⟨y, p₁, c, p₂, hc, rfl⟩ := ih hq
      exact ⟨y, cons e p₁, c, p₂, hc, rfl⟩

lemma le_wt (Λ : ℝ) (h : ∀ a b (e : E a b), -Λ ≤ ℓ a b e) :
    ∀ {a b : N} (p : Walk E a b), -(Λ * p.len) ≤ p.wt ℓ
  | _, _, nil _ => by simp
  | _, _, cons e p => by
    have := le_wt Λ h p; have := h _ _ e
    simp only [wt_cons, len_cons, Nat.cast_add, Nat.cast_one]; linarith

lemma wt_le (Λ : ℝ) (h : ∀ a b (e : E a b), ℓ a b e ≤ Λ) :
    ∀ {a b : N} (p : Walk E a b), p.wt ℓ ≤ Λ * p.len
  | _, _, nil _ => by simp
  | _, _, cons e p => by
    have := wt_le Λ h p; have := h _ _ e
    simp only [wt_cons, len_cons, Nat.cast_add, Nat.cast_one]; linarith

variable [Fintype N]

lemma len_lt_of_nodup {a b : N} (p : Walk E a b) (h : p.support.Nodup) :
    p.len < Fintype.card N := by
  have := h.length_le_card; rw [length_support] at this; omega

/-- A negative closed walk yields one of length at most `|N|`. -/
lemma neg_short : ∀ n {x : N} (r : Walk E x x), r.len = n → r.wt ℓ < 0 →
    ∃ y, ∃ s : Walk E y y, s.len ≤ Fintype.card N ∧ s.wt ℓ < 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x r hn hr
  by_cases hle : r.len ≤ Fintype.card N
  · exact ⟨x, r, hle, hr⟩
  cases r with
  | nil => simp at hle
  | cons e q =>
    have hq : ¬ q.support.Nodup := fun h => by
      have := q.len_lt_of_nodup h; simp at hle; omega
    obtain ⟨y, p₁, c, p₂, hc, rfl⟩ := q.dup_split hq
    simp only [len_cons, len_append, wt_cons, wt_append] at hn hr
    by_cases hc' : c.wt ℓ < 0
    · exact ih c.len (by omega) c rfl hc'
    · exact ih _ (by simp; omega) (cons e (p₁.append p₂)) rfl (by simp; linarith)

/-- Without negative closed walks, every walk can be shortened below `|N|` arcs. -/
lemma short (h0 : ∀ y (c : Walk E y y), 0 ≤ c.wt ℓ) : ∀ n {a b : N} (p : Walk E a b),
    p.len = n → ∃ q : Walk E a b, q.len < Fintype.card N ∧ q.wt ℓ ≤ p.wt ℓ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a b p hn
  by_cases hp : p.support.Nodup
  · exact ⟨p, p.len_lt_of_nodup hp, le_rfl⟩
  obtain ⟨y, p₁, c, p₂, hc, rfl⟩ := p.dup_split hp
  obtain ⟨q, hq, hw⟩ := ih _ (by simp at hn ⊢; omega) (p₁.append p₂) rfl
  exact ⟨q, hq, by simp at hw ⊢; linarith [h0 y c]⟩

end Walk

/-- Data of the face-disjoint graph, with the facts about it that come from [9]. -/
structure Setup (F C Z D : Type u) where
  fc : C → F
  rg : C → C → Prop
  spoke : Z → C → Prop
  tl : D → F
  hd : D → F
  src : D → C
  dst : D → C
  ring_face : ∀ a b, rg a b → fc a = fc b
  ring_conn : ∀ a b, fc a = fc b → Relation.ReflTransGen rg a b
  src_face : ∀ d, fc (src d) = tl d
  dst_face : ∀ d, fc (dst d) = hd d

namespace Setup

variable {F C Z D : Type u} (S : Setup F C Z D)

/-- Arcs of `Ĝ`. -/
inductive Arc : C ⊕ Z → C ⊕ Z → Type u
  | ring {a b : C} (h : S.rg a b) : Arc (.inl a) (.inl b)
  | dual (d : D) : Arc (.inl (S.src d)) (.inl (S.dst d))
  | out {z : Z} {c : C} (h : S.spoke z c) : Arc (.inr z) (.inl c)
  | into {z : Z} {c : C} (h : S.spoke z c) : Arc (.inl c) (.inr z)

/-- Arc lengths of `Ĝ`. -/
def w (lam : D → ℝ) (M : ℝ) : ∀ x y, S.Arc x y → ℝ
  | _, _, .ring _ => 0
  | _, _, .dual d => lam d
  | _, _, .out _ => M
  | _, _, .into _ => M

/-- Dual darts from face `g` to face `h`. -/
abbrev DArc (g h : F) : Type u := {d : D // S.tl d = g ∧ S.hd d = h}

def dw (lam : D → ℝ) : ∀ g h, S.DArc g h → ℝ := fun _ _ d => lam d.1

variable (lam : D → ℝ) (M Λ : ℝ)

/-- A `Ĝ` walk between corners that avoids the star centres is a dual walk. -/
lemma project : ∀ {x y : C ⊕ Z} (p : Walk S.Arc x y), (∀ z, .inr z ∉ p.support) →
    ∀ a b, x = .inl a → y = .inl b →
    ∃ P : Walk S.DArc (S.fc a) (S.fc b), P.wt (S.dw lam) = p.wt (S.w lam M) := by
  intro x y p
  induction p with
  | nil x =>
    intro _ a b ha hb
    obtain rfl : a = b := Sum.inl_injective (ha.symm.trans hb)
    exact ⟨.nil _, by simp⟩
  | cons e q ih =>
    intro hz a b ha hb
    simp only [Walk.support_cons, List.mem_cons, not_or] at hz
    cases e with
    | ring h =>
      obtain rfl := Sum.inl_injective ha
      obtain ⟨P, hP⟩ := ih (fun z => (hz z).2) _ b rfl hb
      rw [S.ring_face _ _ h]
      exact ⟨P, by simp [w, hP]⟩
    | dual d =>
      obtain rfl := Sum.inl_injective ha
      obtain ⟨P, hP⟩ := ih (fun z => (hz z).2) _ b rfl hb
      exact ⟨.cons ⟨d, (S.src_face d).symm, (S.dst_face d).symm⟩ P, by simp [w, dw, hP]⟩
    | out h => cases ha
    | into h => exact absurd q.start_mem (hz _).2

lemma ring_walk {a b : C} (h : Relation.ReflTransGen S.rg a b) :
    ∃ p : Walk S.Arc (.inl a) (.inl b), p.wt (S.w lam M) = 0 := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨.nil _, rfl⟩
  | head h' _ ih =>
    obtain ⟨p, hp⟩ := ih
    exact ⟨.cons (.ring h') p, by simp [w, hp]⟩

/-- A dual walk lifts to a `Ĝ` walk of the same weight between any corners of its end faces. -/
lemma lift : ∀ {g h : F} (P : Walk S.DArc g h) (a b : C), S.fc a = g → S.fc b = h →
    ∃ p : Walk S.Arc (.inl a) (.inl b), p.wt (S.w lam M) = P.wt (S.dw lam) := by
  intro g h P
  induction P with
  | nil g =>
    intro a b ha hb
    obtain ⟨p, hp⟩ := S.ring_walk lam M (S.ring_conn a b (ha.trans hb.symm))
    exact ⟨p, by simp [hp]⟩
  | cons e P ih =>
    intro a b ha hb
    rcases e with ⟨d, hdt, hdh⟩
    obtain ⟨p₀, h₀⟩ :=
      S.ring_walk lam M (S.ring_conn a (S.src d) (by rw [ha, S.src_face, hdt]))
    obtain ⟨p₁, h₁⟩ := ih (S.dst d) b (by rw [S.dst_face, hdh]) hb
    exact ⟨p₀.append (.cons (.dual d) p₁), by simp [w, dw, h₀, h₁]⟩

lemma arc_ge (hΛ0 : 0 ≤ Λ) (hΛ : ∀ d, -Λ ≤ lam d) (hM : 0 ≤ M) :
    ∀ x y (e : S.Arc x y), -Λ ≤ S.w lam M x y e := by
  rintro x y (h | d | h | h) <;> simp only [w]
  · linarith
  · exact hΛ d
  · linarith
  · linarith

section Stars

variable (harc : ∀ x y (e : S.Arc x y), -Λ ≤ S.w lam M x y e)
include harc

lemma to_star : ∀ {x y : C ⊕ Z} (p : Walk S.Arc x y) (c : C) (z : Z), x = .inl c →
    y = .inr z → M + Λ ≤ p.wt (S.w lam M) + Λ * p.len := by
  intro x y p
  induction p with
  | nil x => intro c z hc hz; cases hc.symm.trans hz
  | cons e q ih =>
    intro c z hc hz
    have hq := Walk.le_wt _ Λ harc q
    have he := harc _ _ e
    simp only [Walk.wt_cons, Walk.len_cons, Nat.cast_add, Nat.cast_one]
    cases e with
    | ring h => linarith [ih _ z rfl hz]
    | dual d => linarith [ih _ z rfl hz]
    | out h => cases hc
    | into h => simp only [w]; linarith

lemma from_star {x y : C ⊕ Z} (p : Walk S.Arc x y) (z : Z) (c : C) (hz : x = .inr z)
    (hc : y = .inl c) : M + Λ ≤ p.wt (S.w lam M) + Λ * p.len := by
  cases p with
  | nil x => cases hz.symm.trans hc
  | cons e q =>
    have hq := Walk.le_wt _ Λ harc q
    simp only [Walk.wt_cons, Walk.len_cons, Nat.cast_add, Nat.cast_one]
    cases e with
    | ring h => cases hz
    | dual d => cases hz
    | out h => simp only [w]; linarith
    | into h => cases hz

/-- A walk between corners through a star centre uses two spokes. -/
lemma via_star {a b : C} (p : Walk S.Arc (.inl a) (.inl b)) {z : Z}
    (hz : .inr z ∈ p.support) : 2 * M + 2 * Λ ≤ p.wt (S.w lam M) + Λ * p.len := by
  obtain ⟨p₁, p₂, rfl⟩ := p.split hz
  have h₁ := S.to_star lam M Λ harc p₁ a z rfl rfl
  have h₂ := S.from_star lam M Λ harc p₂ z b rfl rfl
  simp only [Walk.wt_append, Walk.len_append, Nat.cast_add]; linarith

lemma star_closed {z : Z} (r : Walk S.Arc (.inr z) (.inr z)) (hr : r.wt (S.w lam M) < 0) :
    2 * M + 2 * Λ ≤ r.wt (S.w lam M) + Λ * r.len := by
  cases r with
  | nil => simp at hr
  | cons e q =>
    cases e with
    | out h =>
      have := S.to_star lam M Λ harc q _ z rfl rfl
      simp only [Walk.wt_cons, Walk.len_cons, Nat.cast_add, Nat.cast_one, w]; linarith

end Stars

variable [Fintype C] [Fintype Z]

/-- `Ĝ` has a negative cycle iff the dual has one. -/
theorem negCycle_iff (hΛ0 : 0 ≤ Λ) (hΛ : ∀ d, -Λ ≤ lam d)
    (hM : Fintype.card (C ⊕ Z) * Λ < M) :
    (∃ g, ∃ P : Walk S.DArc g g, P.wt (S.dw lam) < 0) ↔
      ∃ x, ∃ p : Walk S.Arc x x, p.wt (S.w lam M) < 0 := by
  have hM0 : 0 ≤ M := le_trans (mul_nonneg (Nat.cast_nonneg _) hΛ0) hM.le
  have harc := S.arc_ge lam M Λ hΛ0 hΛ hM0
  constructor
  · rintro ⟨g, P, hP⟩
    cases P with
    | nil => simp at hP
    | cons e P' =>
      obtain ⟨p, hp⟩ := S.lift lam M (.cons e P') (S.src e.1) (S.src e.1)
        ((S.src_face _).trans e.2.1) ((S.src_face _).trans e.2.1)
      exact ⟨_, p, by rw [hp]; exact hP⟩
  · rintro ⟨x, r, hr⟩
    obtain ⟨y, s, hs, hw⟩ := Walk.neg_short _ _ r rfl hr
    by_cases hz : ∃ z, .inr z ∈ s.support
    · exfalso
      obtain ⟨z, hz⟩ := hz
      have hlen : Λ * s.len ≤ Λ * Fintype.card (C ⊕ Z) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hs) hΛ0
      rcases y with a | z'
      · have := S.via_star lam M Λ harc s hz; linarith
      · have := S.star_closed lam M Λ harc s hw; linarith
    · push Not at hz
      rcases y with a | z'
      · obtain ⟨P, hP⟩ := S.project lam M s hz a a rfl rfl
        exact ⟨_, P, by rw [hP]; exact hw⟩
      · exact absurd s.start_mem (hz z')

/-- Walk-level form of Lemma D. -/
theorem walks (hΛ0 : 0 ≤ Λ) (hΛ : ∀ d, -Λ ≤ lam d) (hM : Fintype.card (C ⊕ Z) * Λ < M)
    (hneg : ∀ g (P : Walk S.DArc g g), 0 ≤ P.wt (S.dw lam)) (a b : C) :
    (∀ P : Walk S.DArc (S.fc a) (S.fc b),
      ∃ p : Walk S.Arc (.inl a) (.inl b), p.wt (S.w lam M) = P.wt (S.dw lam)) ∧
    (∀ p : Walk S.Arc (.inl a) (.inl b), M < p.wt (S.w lam M) ∨
      ∃ P : Walk S.DArc (S.fc a) (S.fc b), P.wt (S.dw lam) ≤ p.wt (S.w lam M)) := by
  have hM0 : 0 ≤ M := le_trans (mul_nonneg (Nat.cast_nonneg _) hΛ0) hM.le
  have harc := S.arc_ge lam M Λ hΛ0 hΛ hM0
  refine ⟨fun P => S.lift lam M P a b rfl rfl, fun p => ?_⟩
  have h0 : ∀ y (c : Walk S.Arc y y), 0 ≤ c.wt (S.w lam M) := by
    intro y c
    by_contra hc
    obtain ⟨g, P, hP⟩ := (S.negCycle_iff lam M Λ hΛ0 hΛ hM).2 ⟨y, c, not_le.1 hc⟩
    exact absurd (hneg g P) (not_le.2 hP)
  obtain ⟨q, hq, hw⟩ := Walk.short _ h0 _ p rfl
  by_cases hz : ∃ z, .inr z ∈ q.support
  · obtain ⟨z, hz⟩ := hz
    have := S.via_star lam M Λ harc q hz
    have : Λ * q.len ≤ Λ * Fintype.card (C ⊕ Z) :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hq.le) hΛ0
    left; linarith
  · push Not at hz
    obtain ⟨P, hP⟩ := S.project lam M q hz a b rfl rfl
    exact .inr ⟨P, hP.le.trans hw⟩

/-- `dist_Ĝ` between corners. -/
noncomputable def gdist (a b : C) : EReal :=
  ⨅ p : Walk S.Arc (.inl a) (.inl b), ((p.wt (S.w lam M) : ℝ) : EReal)

/-- `dist_{G*}` between faces. -/
noncomputable def ddist (g h : F) : EReal := ⨅ P : Walk S.DArc g h, ((P.wt (S.dw lam) : ℝ) : EReal)

/-- **Lemma D.** Without negative dual cycles, `dist_Ĝ(a, b) = dist_{G*}(fc a, fc b)` when the
right side is finite, and `dist_Ĝ(a, b) ≥ M` otherwise. -/
theorem lemmaD [Fintype F] (hsurj : Function.Surjective S.fc) (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ d, |lam d| ≤ Λ) (hM : Fintype.card (C ⊕ Z) * Λ < M)
    (hneg : ∀ g (P : Walk S.DArc g g), 0 ≤ P.wt (S.dw lam)) (a b : C) :
    (S.ddist lam (S.fc a) (S.fc b) ≠ ⊤ → S.gdist lam M a b = S.ddist lam (S.fc a) (S.fc b)) ∧
    (S.ddist lam (S.fc a) (S.fc b) = ⊤ → (M : EReal) ≤ S.gdist lam M a b) := by
  obtain ⟨hl, hr⟩ := S.walks lam M Λ hΛ0 (fun d => (abs_le.1 (hΛ d)).1) hM hneg a b
  unfold gdist ddist
  constructor
  · intro hfin
    obtain ⟨P₀, -⟩ := iInf_lt_iff.1 (lt_top_iff_ne_top.2 hfin)
    obtain ⟨P₁, hP₁, hw₁⟩ := Walk.short _ hneg _ P₀ rfl
    have hcard : (Fintype.card F : ℝ) ≤ Fintype.card (C ⊕ Z) := by
      have := Fintype.card_le_of_surjective _ hsurj
      rw [Fintype.card_sum]; exact_mod_cast this.trans (Nat.le_add_right _ _)
    have hup := Walk.wt_le (S.dw lam) Λ (fun _ _ e => (abs_le.1 (hΛ e.1)).2) P₁
    have h₁ : Λ * P₁.len ≤ Λ * Fintype.card F :=
      mul_le_mul_of_nonneg_left (by exact_mod_cast hP₁.le) hΛ0
    have h₂ := mul_le_mul_of_nonneg_left hcard hΛ0
    have hlt : P₁.wt (S.dw lam) < M := by linarith
    apply le_antisymm
    · refine le_iInf fun P => ?_
      obtain ⟨p, hp⟩ := hl P
      exact (iInf_le _ p).trans (by rw [hp])
    · refine le_iInf fun p => ?_
      rcases hr p with h | ⟨P, hP⟩
      · exact (iInf_le _ P₁).trans (EReal.coe_le_coe_iff.2 (by linarith))
      · exact (iInf_le _ P).trans (EReal.coe_le_coe_iff.2 hP)
  · intro htop
    refine le_iInf fun p => ?_
    rcases hr p with h | ⟨P, -⟩
    · exact EReal.coe_le_coe_iff.2 h.le
    · exact absurd htop (ne_top_of_le_ne_top (EReal.coe_ne_top _) (iInf_le _ P))

end Setup

section Rotation

variable {D V : Type u} [Fintype D] (α φ : Equiv.Perm D) (tail : D → V) (pick : D → Prop)
  [DecidablePred pick]

/-- `Ĝ` from a combinatorial map. Corners are darts, faces are `φ`-orbits, the ring is
`d — φ d`, star centres are vertices with spokes to the darts leaving them. The dual dart of
`d` runs from the face of `d` to the face of `α d`; its arc is `d → φ (α d)` if `d` is picked and
`φ d → α d` otherwise. -/
def rotSetup : Setup (Quotient (Equiv.Perm.SameCycle.setoid φ)) D V D where
  fc d := Quotient.mk _ d
  rg a b := b = φ a ∨ a = φ b
  spoke v d := tail d = v
  tl d := Quotient.mk _ d
  hd d := Quotient.mk _ (α d)
  src d := if pick d then d else φ d
  dst d := if pick d then φ (α d) else α d
  ring_face a b h := by
    apply Quotient.sound
    rcases h with rfl | rfl
    · exact Equiv.Perm.sameCycle_apply_right.2 (Equiv.Perm.SameCycle.refl _ _)
    · exact Equiv.Perm.sameCycle_apply_left.2 (Equiv.Perm.SameCycle.refl _ _)
  ring_conn a b h := by
    obtain ⟨i, rfl⟩ := (Quotient.exact h : Equiv.Perm.SameCycle φ a b).exists_nat_pow_eq
    clear h
    induction i with
    | zero => exact .refl
    | succ i ih => exact ih.tail (.inl (by rw [pow_succ', Equiv.Perm.mul_apply]))
  src_face d := by
    split_ifs
    · rfl
    · exact Quotient.sound (Equiv.Perm.sameCycle_apply_left.2 (Equiv.Perm.SameCycle.refl _ _))
  dst_face d := by
    split_ifs
    · exact Quotient.sound (Equiv.Perm.sameCycle_apply_left.2 (Equiv.Perm.SameCycle.refl _ _))
    · rfl

/-- If `α` is an involution and exactly one dart of each edge is picked, the two arcs of the
edge `{d, α d}` join the same two corners: one `E_C` edge per primal edge, as in [9]. -/
lemma rot_pair (hα : ∀ d, α (α d) = d) (hpick : ∀ d, pick (α d) ↔ ¬ pick d) (d : D)
    (hd : pick d) :
    (rotSetup α φ tail pick).src (α d) = (rotSetup α φ tail pick).dst d ∧
      (rotSetup α φ tail pick).dst (α d) = (rotSetup α φ tail pick).src d := by
  have : ¬ pick (α d) := fun h => (hpick d).1 h hd
  simp [rotSetup, hd, this, hα]

/-- Lemma D for the face-disjoint graph of a combinatorial map. -/
theorem rot_lemmaD [Fintype V] (lam : D → ℝ) (M Λ : ℝ) (hΛ0 : 0 ≤ Λ) (hΛ : ∀ d, |lam d| ≤ Λ)
    (hM : Fintype.card (D ⊕ V) * Λ < M) :
    let S := rotSetup α φ tail pick
    ((∃ g, ∃ P : Walk S.DArc g g, P.wt (S.dw lam) < 0) ↔
        ∃ x, ∃ p : Walk S.Arc x x, p.wt (S.w lam M) < 0) ∧
      ((∀ g (P : Walk S.DArc g g), 0 ≤ P.wt (S.dw lam)) → ∀ a b : D,
        (S.ddist lam (S.fc a) (S.fc b) ≠ ⊤ → S.gdist lam M a b = S.ddist lam (S.fc a) (S.fc b)) ∧
        (S.ddist lam (S.fc a) (S.fc b) = ⊤ → (M : EReal) ≤ S.gdist lam M a b)) := by
  intro S
  have : Fintype (Quotient (Equiv.Perm.SameCycle.setoid φ)) := Fintype.ofFinite _
  refine ⟨S.negCycle_iff lam M Λ hΛ0 (fun d => (abs_le.1 (hΛ d)).1) hM, fun hneg a b => ?_⟩
  exact S.lemmaD lam M Λ (fun q => q.inductionOn fun d => ⟨d, rfl⟩) hΛ0 hΛ hM hneg a b

end Rotation

end SsspFlow.FaceDisjoint
