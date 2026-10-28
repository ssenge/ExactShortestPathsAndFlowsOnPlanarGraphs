import SsspFlow.LemmaV

/-!
# Lemma 16′: one level of the labels

The inductive step of Lemma 16′ in `notes/LEMMA15.md` §6, in the setting of `LemmaV.lean`
(arc lengths in `[0, ∞]`, `dist adj w X a b` the least length of a walk inside `X`).

A bag `X` with separator `S`, a child `Xi ⊆ X` with hub set `Hi ⊇ S ∩ Xi`, child labels
`estI` within `[dist_{G[Xi]}, λᵢ · dist_{G[Xi]}]`, and labels `δ` from the oracle of `H_X` within
`[dist_{G[X]}, λ · dist_{G[X]}]` between `S` and a hub `h` of `X`. For `v ∈ Xi ∖ S` the label is
`d̃(v, h) = min (estI v h if h ∈ Xi) (min_{t ∈ S ∩ Xi} estI v t + δ t h)`, and symmetrically for
`d̃(h, v)`. Both lie in `[dist_{G[X]}, λ · dist_{G[X]}]` when `λᵢ ≤ λ` (`labelOut`, `labelIn`).

The one structural hypothesis is `hclose`, which is (7c′) together with (7b) for arcs in both
directions: an arc of `G[X]` at a vertex of `Xi ∖ S` stays in `Xi`.

## Not formalized
The construction of the bags, of `H_X` and of its oracle (Lemma 15′), and the broadcast.
-/

open scoped ENNReal

namespace SsspFlow

universe u

variable {V : Type u} {adj : V → V → Prop}

namespace Walk

/-- The reverse walk, in the reversed digraph. -/
def reverse : {a b : V} → Walk adj a b → Walk (flip adj) b a
  | _, _, nil a => nil a
  | _, _, cons e p => (reverse p).append (cons e (nil _))

lemma support_append : ∀ {a b c : V} (p : Walk adj a b) (q : Walk adj b c) (z : V),
    z ∈ (p.append q).support → z ∈ p.support ∨ z ∈ q.support
  | _, _, _, nil _, q, z, h => Or.inr h
  | _, _, _, cons _ p, q, z, h => by
    simp only [append, support_cons, List.mem_cons] at h ⊢
    rcases h with rfl | h
    · exact Or.inl (Or.inl rfl)
    · rcases support_append p q z h with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h

lemma mem_support_reverse : ∀ {a b : V} (p : Walk adj a b) (z : V),
    z ∈ p.reverse.support → z ∈ p.support
  | _, _, nil _, z, h => h
  | a, _, cons (b := b) _ p, z, h => by
    rcases support_append _ _ z h with h | h
    · exact List.mem_cons_of_mem _ (mem_support_reverse p z h)
    · have : z = b ∨ z = a := by simpa [Walk.support] using h
      rcases this with rfl | rfl
      · exact List.mem_cons_of_mem _ p.start_mem
      · exact List.mem_cons_self ..

lemma wt_reverse (w : V → V → ℝ≥0∞) : ∀ {a b : V} (p : Walk adj a b),
    p.reverse.wt (flip w) = p.wt w
  | _, _, nil _ => rfl
  | _, _, cons _ p => by
    rw [reverse, wt_append, wt_reverse w p]
    simp [Walk.wt, flip, add_comm]

end Walk

lemma dist_flip_le (w : V → V → ℝ≥0∞) (X : Set V) (a b : V) :
    dist (flip adj) (flip w) X b a ≤ dist adj w X a b := by
  simp only [dist, le_iInf_iff]
  intro p hp
  rw [← Walk.wt_reverse w p]
  exact iInf₂_le p.reverse fun z hz => hp z (Walk.mem_support_reverse p z hz)

lemma dist_flip (w : V → V → ℝ≥0∞) (X : Set V) (a b : V) :
    dist (flip adj) (flip w) X b a = dist adj w X a b :=
  le_antisymm (dist_flip_le w X a b) (dist_flip_le (adj := flip adj) (flip w) X b a)

lemma dist_mono (w : V → V → ℝ≥0∞) {X Y : Set V} (h : X ⊆ Y) (a b : V) :
    dist adj w Y a b ≤ dist adj w X a b := by
  simp only [dist, le_iInf_iff]
  exact fun p hp => iInf₂_le p fun z hz => h (hp z hz)

lemma dist_triangle' (w : V → V → ℝ≥0∞) (X : Set V) (a b c : V) :
    dist adj w X a c ≤ dist adj w X a b + dist adj w X b c := by
  simp only [dist, ENNReal.iInf_add, ENNReal.add_iInf, le_iInf_iff]
  intro q hq p hp
  rw [← Walk.wt_append]
  refine iInf₂_le (p.append q) fun z hz => ?_
  rcases Walk.support_append p q z hz with h | h
  · exact hp z h
  · exact hq z h

variable (X Xi S : Set V)

/-- A walk in `X` from `Xi ∖ S` stays in `Xi ∖ S`, or reaches `S` first at some `t ∈ Xi`. -/
lemma first_hit (w : V → V → ℝ≥0∞)
    (hclose : ∀ a b, adj a b → a ∈ Xi → a ∉ S → b ∈ X → b ∈ Xi) :
    ∀ {a b : V} (p : Walk adj a b), a ∈ Xi → (∀ z ∈ p.support, z ∈ X) →
      (∀ z ∈ p.support, z ∈ Xi) ∨
      ∃ t ∈ S, t ∈ Xi ∧ ∃ (p₁ : Walk adj a t) (p₂ : Walk adj t b),
        (∀ z ∈ p₁.support, z ∈ Xi) ∧ (∀ z ∈ p₂.support, z ∈ X) ∧ p₁.wt w + p₂.wt w = p.wt w
  | _, _, .nil a, ha, _ => Or.inl (by simpa using ha)
  | a, b, .cons e p, ha, hX => by
    by_cases haS : a ∈ S
    · exact Or.inr ⟨a, haS, ha, .nil a, .cons e p, by simpa using ha, hX, by simp⟩
    have hX' : ∀ z ∈ p.support, z ∈ X := fun z hz => hX z (List.mem_cons_of_mem _ hz)
    have hc := hclose _ _ e ha haS (hX' _ p.start_mem)
    rcases first_hit w hclose p hc hX' with h | ⟨t, htS, ht, p₁, p₂, h₁, h₂, hw⟩
    · exact Or.inl (by simpa [ha] using h)
    · refine Or.inr ⟨t, htS, ht, .cons e p₁, p₂, by simpa [ha] using h₁, h₂, ?_⟩
      simp only [Walk.wt_cons, ← hw, add_assoc]

/-- The label `d̃(v, h)` of a non-hub `v`. -/
noncomputable def lbl (estI δ : V → V → ℝ≥0∞) (v h : V) : ℝ≥0∞ :=
  min (⨅ (_ : h ∈ Xi), estI v h) (⨅ t ∈ S ∩ Xi, estI v t + δ t h)

/-- **Lemma 16′, one level, direction `v → h`.** -/
theorem labelOut (w : V → V → ℝ≥0∞) (Hi : Set V) (estI δ : V → V → ℝ≥0∞) (lamI lam : ℝ≥0∞)
    (hXi : Xi ⊆ X) (hSi : ∀ t ∈ S, t ∈ Xi → t ∈ Hi)
    (hclose : ∀ a b, adj a b → a ∈ Xi → a ∉ S → b ∈ X → b ∈ Xi)
    (lo_i : ∀ v t, v ∈ Xi → t ∈ Hi → dist adj w Xi v t ≤ estI v t)
    (hi_i : ∀ v t, v ∈ Xi → t ∈ Hi → estI v t ≤ lamI * dist adj w Xi v t)
    (v h : V) (hv : v ∈ Xi) (hhi : h ∈ Xi → h ∈ Hi)
    (lo_δ : ∀ t ∈ S, dist adj w X t h ≤ δ t h)
    (hi_δ : ∀ t ∈ S, δ t h ≤ lam * dist adj w X t h)
    (hlam : lamI ≤ lam) (hlam1 : 1 ≤ lam) (hlamT : lam ≠ ∞) :
    dist adj w X v h ≤ lbl Xi S estI δ v h ∧ lbl Xi S estI δ v h ≤ lam * dist adj w X v h := by
  constructor
  · refine le_min (le_iInf fun hh => ?_) (le_iInf₂ fun t ht => ?_)
    · exact (dist_mono w hXi v h).trans (lo_i v h hv (hhi hh))
    · calc dist adj w X v h ≤ dist adj w X v t + dist adj w X t h := dist_triangle' w X v t h
        _ ≤ estI v t + δ t h := by
          gcongr
          · exact (dist_mono w hXi v t).trans (lo_i v t hv (hSi t ht.1 ht.2))
          · exact lo_δ t ht.1
  · have h0 : lam ≠ 0 := (lt_of_lt_of_le one_pos hlam1).ne'
    conv_rhs => rw [dist, ENNReal.mul_iInf_of_ne h0 hlamT]
    refine le_iInf fun p => ?_
    rw [ENNReal.mul_iInf_of_ne h0 hlamT]
    refine le_iInf fun hp => ?_
    rcases first_hit X Xi S w hclose p hv hp with hin | ⟨t, htS, ht, p₁, p₂, h₁, h₂, hw⟩
    · have hh : h ∈ Xi := hin h p.end_mem
      calc lbl Xi S estI δ v h ≤ estI v h := (min_le_left _ _).trans (iInf_le _ hh)
        _ ≤ lamI * dist adj w Xi v h := hi_i v h hv (hhi hh)
        _ ≤ lam * p.wt w := mul_le_mul' hlam (iInf₂_le p hin)
    · calc lbl Xi S estI δ v h ≤ estI v t + δ t h :=
            (min_le_right _ _).trans (iInf₂_le t ⟨htS, ht⟩)
        _ ≤ lamI * dist adj w Xi v t + lam * dist adj w X t h :=
            add_le_add (hi_i v t hv (hSi t htS ht)) (hi_δ t htS)
        _ ≤ lam * p₁.wt w + lam * p₂.wt w :=
            add_le_add (mul_le_mul' hlam (iInf₂_le p₁ h₁)) (mul_le_mul' le_rfl (iInf₂_le p₂ h₂))
        _ = lam * p.wt w := by rw [← mul_add, hw]

/-- **Lemma 16′, one level, direction `h → v`**: `labelOut` in the reversed digraph. -/
theorem labelIn (w : V → V → ℝ≥0∞) (Hi : Set V) (estI δ : V → V → ℝ≥0∞) (lamI lam : ℝ≥0∞)
    (hXi : Xi ⊆ X) (hSi : ∀ t ∈ S, t ∈ Xi → t ∈ Hi)
    (hclose : ∀ a b, adj a b → b ∈ Xi → b ∉ S → a ∈ X → a ∈ Xi)
    (lo_i : ∀ v t, v ∈ Xi → t ∈ Hi → dist adj w Xi t v ≤ estI t v)
    (hi_i : ∀ v t, v ∈ Xi → t ∈ Hi → estI t v ≤ lamI * dist adj w Xi t v)
    (v h : V) (hv : v ∈ Xi) (hhi : h ∈ Xi → h ∈ Hi)
    (lo_δ : ∀ t ∈ S, dist adj w X h t ≤ δ h t)
    (hi_δ : ∀ t ∈ S, δ h t ≤ lam * dist adj w X h t)
    (hlam : lamI ≤ lam) (hlam1 : 1 ≤ lam) (hlamT : lam ≠ ∞) :
    dist adj w X h v ≤ lbl Xi S (flip estI) (flip δ) v h ∧
      lbl Xi S (flip estI) (flip δ) v h ≤ lam * dist adj w X h v := by
  have := labelOut (adj := flip adj) X Xi S (flip w) Hi (flip estI) (flip δ) lamI lam hXi hSi
    (fun a b e ha haS hb => hclose b a e ha haS hb)
    (fun v t hv ht => (dist_flip w Xi t v).le.trans (lo_i v t hv ht))
    (fun v t hv ht => (hi_i v t hv ht).trans_eq (by rw [dist_flip]))
    v h hv hhi
    (fun t ht => (dist_flip w X h t).le.trans (lo_δ t ht))
    (fun t ht => (hi_δ t ht).trans_eq (by rw [dist_flip]))
    hlam hlam1 hlamT
  rwa [dist_flip] at this

end SsspFlow
