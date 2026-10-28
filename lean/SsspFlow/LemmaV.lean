import Mathlib.Basic.ENNReal.Inv

/-!
# Lemma V: virtual-source queries over a bag hierarchy

Setting of Lemma V in `sssp_flow/NOTES.md` (Theorem A). A digraph `adj` on `V` with arc lengths
`w a b ∈ [0, ∞]` and a virtual source `σ` joined to every `u` by an arc of length `φ u`, so
`d(σ, v) = min_u φ u + dist_G(u, v)` (`dsrc`). Bags `bag x` (indexed by `ι`, child relation `kid`,
well founded) carry hub sets `hub x`. Each bag supplies estimates `est x u h` and `est x h v` for
`u, v ∈ bag x`, `h ∈ hub x`, that never underestimate `dist_{G[bag x]}` and overestimate it by at
most the factor `1 + ε`. The query is
* `agg x h = min_{u ∈ bag x} φ u + est x u h` (one convergecast per bag),
* `query v = min_{x ∋ v} min_{h ∈ hub x} agg x h + est x h v` (over all bags containing `v`),

and `lemmaV` proves `d(σ, v) ≤ query v ≤ (1 + ε) · d(σ, v)`.

Hierarchy assumptions (`Hierarchy`), the BDD Property 7(b) stated with hubs:
* `root_bag`: some bag contains every vertex;
* `cover`, `uniq`: a non-hub vertex of a bag lies in exactly one child;
* `edge`: an arc between two non-hub vertices of a bag lies inside a common child.

If the separator `S_x` is contained in `hub x`, the usual versions with `S_x` imply these. A leaf
has no children, so `cover` makes all its vertices hubs; this is the leaf-local term of the notes.
No finiteness is needed: minima are infima in `ℝ≥0∞`, and `⊤` encodes "unreachable".

## Not formalized
The CONGEST implementation and round count, the construction of the hierarchy and of the
estimates (LTY Lemma 16), and the RHMGZ reduction that calls this oracle.
-/

open scoped ENNReal

namespace SsspFlow

universe u v

/-- Walks in the digraph `adj`. -/
inductive Walk {V : Type u} (adj : V → V → Prop) : V → V → Type u
  | nil (a : V) : Walk adj a a
  | cons {a b c : V} (e : adj a b) (p : Walk adj b c) : Walk adj a c

namespace Walk

variable {V : Type u} {adj : V → V → Prop}

/-- Vertices visited, in order. -/
def support : {a b : V} → Walk adj a b → List V
  | a, _, nil _ => [a]
  | a, _, cons _ p => a :: p.support

/-- Length of the walk under arc lengths `w`. -/
def wt (w : V → V → ℝ≥0∞) : {a b : V} → Walk adj a b → ℝ≥0∞
  | _, _, nil _ => 0
  | _, _, @cons _ _ a m _ _ p => w a m + p.wt w

def append : {a b c : V} → Walk adj a b → Walk adj b c → Walk adj a c
  | _, _, _, nil _, q => q
  | _, _, _, cons e p, q => cons e (p.append q)

variable (w : V → V → ℝ≥0∞)

@[simp] lemma support_nil (a : V) : (nil a : Walk adj a a).support = [a] := rfl

@[simp] lemma support_cons {a b c : V} (e : adj a b) (p : Walk adj b c) :
    (cons e p).support = a :: p.support := rfl

@[simp] lemma wt_nil (a : V) : (nil a : Walk adj a a).wt w = 0 := rfl

@[simp] lemma wt_cons {a b c : V} (e : adj a b) (p : Walk adj b c) :
    (cons e p).wt w = w a b + p.wt w := rfl

lemma wt_append : ∀ {a b c : V} (p : Walk adj a b) (q : Walk adj b c),
    (p.append q).wt w = p.wt w + q.wt w
  | _, _, _, nil _, q => by simp [append]
  | _, _, _, cons e p, q => by simp [append, wt_append p q, add_assoc]

lemma start_mem : ∀ {a b : V} (p : Walk adj a b), a ∈ p.support
  | _, _, nil _ => by simp
  | _, _, cons _ _ => by simp

lemma end_mem : ∀ {a b : V} (p : Walk adj a b), b ∈ p.support
  | _, _, nil _ => by simp
  | _, _, cons _ p => by simp [end_mem p]

/-- Cut a walk at a visited vertex `h`. -/
lemma split {a b h : V} (p : Walk adj a b) (hp : h ∈ p.support) :
    ∃ (p₁ : Walk adj a h) (p₂ : Walk adj h b), p₁.support ⊆ p.support ∧
      p₂.support ⊆ p.support ∧ p₁.wt w + p₂.wt w = p.wt w := by
  induction p with
  | nil a =>
    obtain rfl : h = a := by simpa using hp
    exact ⟨nil h, nil h, by simp, by simp, by simp⟩
  | cons e p ih =>
    rcases List.mem_cons.1 hp with rfl | hp
    · exact ⟨nil h, cons e p, by simp, List.Subset.refl _, by simp⟩
    · obtain ⟨p₁, p₂, h₁, h₂, hw⟩ := ih hp
      refine ⟨cons e p₁, p₂, ?_, fun z hz => List.mem_cons_of_mem _ (h₂ hz), ?_⟩
      · simpa using List.cons_subset_cons _ h₁
      · simp [← hw, add_assoc]

end Walk

/-- A bag hierarchy with hub sets; see the module docstring. -/
structure Hierarchy (V : Type u) (ι : Type v) (adj : V → V → Prop) where
  bag : ι → Set V
  hub : ι → Set V
  kid : ι → ι → Prop
  wf : WellFounded kid
  root : ι
  root_bag : ∀ z, z ∈ bag root
  cover : ∀ x z, z ∈ bag x → z ∉ hub x → ∃ c, kid c x ∧ z ∈ bag c
  uniq : ∀ x c c' z, kid c x → kid c' x → z ∈ bag x → z ∉ hub x → z ∈ bag c → z ∈ bag c' →
    c = c'
  edge : ∀ x a b, adj a b → a ∈ bag x → b ∈ bag x → a ∉ hub x → b ∉ hub x →
    ∃ c, kid c x ∧ a ∈ bag c ∧ b ∈ bag c

variable {V : Type u} {ι : Type v} {adj : V → V → Prop}

/-- `dist_{G[X]}(a, b)`: least length of a walk from `a` to `b` that stays in `X`. -/
noncomputable def dist (adj : V → V → Prop) (w : V → V → ℝ≥0∞) (X : Set V) (a b : V) : ℝ≥0∞ :=
  ⨅ (p : Walk adj a b) (_ : ∀ z ∈ p.support, z ∈ X), p.wt w

/-- `d(σ, v)` for the virtual source `σ` with arcs `σ → u` of length `φ u`. -/
noncomputable def dsrc (adj : V → V → Prop) (w : V → V → ℝ≥0∞) (φ : V → ℝ≥0∞) (v : V) : ℝ≥0∞ :=
  ⨅ a, φ a + dist adj w Set.univ a v

lemma dist_triangle (w : V → V → ℝ≥0∞) (X : Set V) (a b c : V) :
    dist adj w Set.univ a c ≤ dist adj w X a b + dist adj w X b c := by
  simp only [dist, ENNReal.iInf_add, ENNReal.add_iInf, le_iInf_iff]
  intro q _ p _
  rw [← Walk.wt_append]
  exact iInf₂_le (p.append q) (by simp)

namespace Hierarchy

variable (H : Hierarchy V ι adj)

/-- A walk inside bag `x` that avoids `hub x` stays inside one child. -/
lemma one_kid (x : ι) {a b : V} (p : Walk adj a b) (hX : ∀ z ∈ p.support, z ∈ H.bag x)
    (hH : ∀ z ∈ p.support, z ∉ H.hub x) : ∃ c, H.kid c x ∧ ∀ z ∈ p.support, z ∈ H.bag c := by
  induction p with
  | nil a =>
    obtain ⟨c, hc, ha⟩ := H.cover x a (hX a (by simp)) (hH a (by simp))
    exact ⟨c, hc, by simpa using ha⟩
  | cons e p ih =>
    simp only [Walk.support_cons, List.mem_cons, forall_eq_or_imp] at hX hH
    obtain ⟨c, hc, hp⟩ := ih hX.2 hH.2
    have hb := p.start_mem
    obtain ⟨c', hc', ha', hb'⟩ := H.edge x _ _ e hX.1 (hX.2 _ hb) hH.1 (hH.2 _ hb)
    obtain rfl := H.uniq x c c' _ hc hc' (hX.2 _ hb) (hH.2 _ hb) (hp _ hb) hb'
    exact ⟨c, hc, by simpa [ha'] using hp⟩

/-- Deepest-bag argument: a walk inside bag `x` passes through a hub `h` of some bag `y` below
`x`, and both halves stay inside `y`. -/
lemma descend (w : V → V → ℝ≥0∞) (x : ι) {a b : V} (p : Walk adj a b)
    (hX : ∀ z ∈ p.support, z ∈ H.bag x) :
    ∃ y h, h ∈ H.hub y ∧ ∃ (p₁ : Walk adj a h) (p₂ : Walk adj h b),
      (∀ z ∈ p₁.support, z ∈ H.bag y) ∧ (∀ z ∈ p₂.support, z ∈ H.bag y) ∧
      p₁.wt w + p₂.wt w = p.wt w := by
  induction x using H.wf.induction generalizing a b with
  | _ x ih =>
  by_cases hh : ∃ h ∈ p.support, h ∈ H.hub x
  · obtain ⟨h, hp, hh⟩ := hh
    obtain ⟨p₁, p₂, h₁, h₂, hw⟩ := p.split w hp
    exact ⟨x, h, hh, p₁, p₂, fun z hz => hX z (h₁ hz), fun z hz => hX z (h₂ hz), hw⟩
  · push Not at hh
    obtain ⟨c, hc, hp⟩ := H.one_kid x p hX hh
    exact ih c hc p hp

variable (φ : V → ℝ≥0∞) (est : ι → V → V → ℝ≥0∞)

/-- `A_x(h) = min_{u ∈ bag x} φ u + est x u h`. -/
noncomputable def agg (x : ι) (h : V) : ℝ≥0∞ := ⨅ a ∈ H.bag x, φ a + est x a h

/-- The all-bags query of Lemma V. -/
noncomputable def query (z : V) : ℝ≥0∞ := ⨅ (x) (_ : z ∈ H.bag x) (h ∈ H.hub x), H.agg φ est x h + est x h z

/-- **Lemma V.** -/
theorem lemmaV (w : V → V → ℝ≥0∞) (ε : ℝ≥0∞) (hε : ε ≠ ∞)
    (lo₁ : ∀ x a h, a ∈ H.bag x → h ∈ H.hub x → dist adj w (H.bag x) a h ≤ est x a h)
    (lo₂ : ∀ x h z, z ∈ H.bag x → h ∈ H.hub x → dist adj w (H.bag x) h z ≤ est x h z)
    (hi₁ : ∀ x a h, a ∈ H.bag x → h ∈ H.hub x →
      est x a h ≤ (1 + ε) * dist adj w (H.bag x) a h)
    (hi₂ : ∀ x h z, z ∈ H.bag x → h ∈ H.hub x →
      est x h z ≤ (1 + ε) * dist adj w (H.bag x) h z)
    (z : V) :
    dsrc adj w φ z ≤ H.query φ est z ∧ H.query φ est z ≤ (1 + ε) * dsrc adj w φ z := by
  constructor
  · simp only [query, agg, ENNReal.iInf_add, le_iInf_iff]
    intro x hz h hh a ha
    calc dsrc adj w φ z ≤ φ a + dist adj w Set.univ a z := iInf_le (fun a => _ + _) a
      _ ≤ φ a + (dist adj w (H.bag x) a h + dist adj w (H.bag x) h z) := by
          gcongr; exact dist_triangle w _ a h z
      _ ≤ φ a + est x a h + est x h z := by
          rw [add_assoc]; gcongr
          · exact lo₁ x a h ha hh
          · exact lo₂ x h z hz hh
  · have hc0 : (1 + ε) ≠ 0 := (lt_of_lt_of_le one_pos le_self_add).ne'
    have hcT : (1 + ε) ≠ ∞ := ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hε⟩
    simp only [dsrc, dist, ENNReal.add_iInf, ENNReal.mul_iInf_of_ne hc0 hcT, le_iInf_iff]
    intro a p _
    obtain ⟨y, h, hh, p₁, p₂, h₁, h₂, hw⟩ := H.descend w H.root p (fun z _ => H.root_bag z)
    have hz : z ∈ H.bag y := h₂ _ p₂.end_mem
    have ha : a ∈ H.bag y := h₁ _ p₁.start_mem
    calc H.query φ est z ≤ H.agg φ est y h + est y h z := (iInf₂_le y hz).trans (iInf₂_le h hh)
      _ ≤ φ a + est y a h + est y h z := by gcongr; exact iInf₂_le a ha
      _ ≤ φ a + (1 + ε) * p₁.wt w + (1 + ε) * p₂.wt w := by
          gcongr
          · exact (hi₁ y a h ha hh).trans (by gcongr; exact iInf₂_le p₁ h₁)
          · exact (hi₂ y h z hz hh).trans (by gcongr; exact iInf₂_le p₂ h₂)
      _ ≤ (1 + ε) * (φ a + p.wt w) := by
          rw [← hw, mul_add, mul_add, add_assoc]
          gcongr
          exact le_mul_of_one_le_left (by simp) le_self_add

end Hierarchy

end SsspFlow
