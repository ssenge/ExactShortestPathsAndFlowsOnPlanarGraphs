import SsspFlow.LemmaV

/-!
# Lemma V for region bags

The region form of the bag hierarchy (`sssp_flow/LEMMA15.md` §9). A bag `x` carries, besides
its vertex set `bag x`, a set of arcs `arc x` (the arcs of its region graph `R_x`), and the
estimates approximate `dist_{R_x}`: the least length of a walk all of whose arcs lie in `arc x`.
The induced version in `LemmaV.lean` is the special case `arc x a b ↔ a ∈ bag x ∧ b ∈ bag x`.

Assumptions (`RHierarchy`):
* `root_arc`, `root_bag`: the root holds every arc and every vertex;
* `arc_bag`: the ends of an arc of a bag lie in the bag;
* `cover`, `uniq`: a non-hub vertex of a bag lies in exactly one child;
* `edge`: an arc of a bag between two non-hub vertices is an arc of some child. This is
  Lemma B1(b) of §9 (it even holds with one non-hub end).

`lemmaV` proves `d(σ, v) ≤ query v ≤ (1 + ε) · d(σ, v)` for the all-bags query.
-/

open scoped ENNReal

namespace SsspFlow

universe u v

namespace Walk

variable {V : Type u} {adj : V → V → Prop}

/-- Every arc of the walk satisfies `A`. -/
def arcsIn (A : V → V → Prop) : {a b : V} → Walk adj a b → Prop
  | _, _, nil _ => True
  | _, _, @cons _ _ a m _ _ p => A a m ∧ p.arcsIn A

@[simp] lemma arcsIn_nil (A : V → V → Prop) (a : V) : (nil a : Walk adj a a).arcsIn A := trivial

@[simp] lemma arcsIn_cons (A : V → V → Prop) {a b c : V} (e : adj a b) (p : Walk adj b c) :
    (cons e p).arcsIn A ↔ A a b ∧ p.arcsIn A := Iff.rfl

lemma arcsIn_of_adj {A : V → V → Prop} (hA : ∀ a b, adj a b → A a b) :
    ∀ {a b : V} (p : Walk adj a b), p.arcsIn A
  | _, _, nil _ => trivial
  | _, _, cons e p => (arcsIn_cons A e p).2 ⟨hA _ _ e, arcsIn_of_adj hA p⟩

/-- Cut a walk at a visited vertex `h`; both halves keep the arc property. -/
lemma splitA (w : V → V → ℝ≥0∞) (A : V → V → Prop) {a b h : V} (p : Walk adj a b)
    (hA : p.arcsIn A) (hp : h ∈ p.support) :
    ∃ (p₁ : Walk adj a h) (p₂ : Walk adj h b), p₁.arcsIn A ∧ p₂.arcsIn A ∧
      p₁.wt w + p₂.wt w = p.wt w := by
  induction p with
  | nil a =>
    obtain rfl : h = a := by simpa using hp
    exact ⟨nil h, nil h, trivial, trivial, by simp⟩
  | cons e p ih =>
    have hA' := (arcsIn_cons A e p).1 hA
    rcases List.mem_cons.1 hp with rfl | hp
    · exact ⟨nil h, cons e p, trivial, hA, by simp⟩
    · obtain ⟨p₁, p₂, h₁, h₂, hw⟩ := ih hA'.2 hp
      exact ⟨cons e p₁, p₂, (arcsIn_cons A e p₁).2 ⟨hA'.1, h₁⟩, h₂, by simp [← hw, add_assoc]⟩

/-- The vertices of a walk with arcs in `A` lie in `X`, if `A` stays in `X` and the walk
starts in `X`. -/
lemma support_sub {A : V → V → Prop} {X : Set V} (hX : ∀ a b, A a b → a ∈ X ∧ b ∈ X) :
    ∀ {a b : V} (p : Walk adj a b), p.arcsIn A → a ∈ X → ∀ z ∈ p.support, z ∈ X
  | _, _, nil _, _, ha, z, hz => by simp at hz; subst hz; exact ha
  | _, _, cons e p, hA, ha, z, hz => by
    have hA' := (arcsIn_cons A e p).1 hA
    rcases List.mem_cons.1 hz with rfl | hz
    · exact ha
    · exact support_sub hX p hA'.2 (hX _ _ hA'.1).2 z hz

end Walk

/-- `dist_{R}(a, b)`: least length of a walk from `a` to `b` all of whose arcs satisfy `A`. -/
noncomputable def distR (adj : V → V → Prop) (w : V → V → ℝ≥0∞) (A : V → V → Prop) (a b : V) :
    ℝ≥0∞ :=
  ⨅ (p : Walk adj a b) (_ : p.arcsIn A), p.wt w

lemma distR_triangle {V : Type u} {adj : V → V → Prop} (w : V → V → ℝ≥0∞) (A : V → V → Prop)
    (a b c : V) : dist adj w Set.univ a c ≤ distR adj w A a b + distR adj w A b c := by
  simp only [distR, ENNReal.iInf_add, ENNReal.add_iInf, le_iInf_iff]
  intro q _ p _
  rw [← Walk.wt_append]
  exact iInf₂_le (p.append q) (by simp)

/-- A bag hierarchy of region bags with hub sets; see the module docstring. -/
structure RHierarchy (V : Type u) (ι : Type v) (adj : V → V → Prop) where
  bag : ι → Set V
  arc : ι → V → V → Prop
  hub : ι → Set V
  kid : ι → ι → Prop
  wf : WellFounded kid
  root : ι
  root_bag : ∀ z, z ∈ bag root
  root_arc : ∀ a b, adj a b → arc root a b
  arc_bag : ∀ x a b, arc x a b → a ∈ bag x ∧ b ∈ bag x
  cover : ∀ x z, z ∈ bag x → z ∉ hub x → ∃ c, kid c x ∧ z ∈ bag c
  uniq : ∀ x c c' z, kid c x → kid c' x → z ∈ bag x → z ∉ hub x → z ∈ bag c → z ∈ bag c' →
    c = c'
  edge : ∀ x a b, arc x a b → a ∉ hub x → b ∉ hub x → ∃ c, kid c x ∧ arc c a b

namespace RHierarchy

variable {V : Type u} {ι : Type v} {adj : V → V → Prop}
variable (H : RHierarchy V ι adj)

/-- A walk in the region of bag `x` that avoids `hub x` stays in the region of one child. -/
lemma one_kid (x : ι) {a b : V} (p : Walk adj a b) (hA : p.arcsIn (H.arc x)) (ha : a ∈ H.bag x)
    (hH : ∀ z ∈ p.support, z ∉ H.hub x) :
    ∃ c, H.kid c x ∧ p.arcsIn (H.arc c) ∧ a ∈ H.bag c := by
  induction p with
  | nil a =>
    obtain ⟨c, hc, ha'⟩ := H.cover x a ha (hH a (by simp))
    exact ⟨c, hc, trivial, ha'⟩
  | @cons a m _ e p ih =>
    simp only [Walk.support_cons, List.mem_cons, forall_eq_or_imp] at hH
    have hA' := (Walk.arcsIn_cons _ e p).1 hA
    have hm : m ∈ H.bag x := (H.arc_bag x a m hA'.1).2
    obtain ⟨c, hc, hp, hmc⟩ := ih hA'.2 hm hH.2
    obtain ⟨c', hc', hac'⟩ := H.edge x a m hA'.1 hH.1 (hH.2 m p.start_mem)
    obtain rfl := H.uniq x c c' m hc hc' hm (hH.2 m p.start_mem) hmc (H.arc_bag c' a m hac').2
    exact ⟨c, hc, (Walk.arcsIn_cons _ e p).2 ⟨hac', hp⟩, (H.arc_bag c a m hac').1⟩

/-- Deepest-bag argument for region bags. -/
lemma descend (w : V → V → ℝ≥0∞) (x : ι) {a b : V} (p : Walk adj a b)
    (hA : p.arcsIn (H.arc x)) (ha : a ∈ H.bag x) :
    ∃ y h, h ∈ H.hub y ∧ ∃ (p₁ : Walk adj a h) (p₂ : Walk adj h b),
      p₁.arcsIn (H.arc y) ∧ p₂.arcsIn (H.arc y) ∧ a ∈ H.bag y ∧ h ∈ H.bag y ∧ b ∈ H.bag y ∧
      p₁.wt w + p₂.wt w = p.wt w := by
  induction x using H.wf.induction generalizing a b with
  | _ x ih =>
  have hsub := Walk.support_sub (H.arc_bag x) p hA ha
  by_cases hh : ∃ h ∈ p.support, h ∈ H.hub x
  · obtain ⟨h, hp, hh⟩ := hh
    obtain ⟨p₁, p₂, h₁, h₂, hw⟩ := p.splitA w (H.arc x) hA hp
    exact ⟨x, h, hh, p₁, p₂, h₁, h₂, ha, hsub h hp, hsub b p.end_mem, hw⟩
  · push Not at hh
    obtain ⟨c, hc, hp, hac⟩ := H.one_kid x p hA ha hh
    exact ih c hc p hp hac

variable (φ : V → ℝ≥0∞) (est : ι → V → V → ℝ≥0∞)

/-- `A_x(h) = min_{u ∈ bag x} φ u + est x u h`. -/
noncomputable def agg (x : ι) (h : V) : ℝ≥0∞ := ⨅ a ∈ H.bag x, φ a + est x a h

/-- The all-bags query of Lemma V. -/
noncomputable def query (z : V) : ℝ≥0∞ :=
  ⨅ (x) (_ : z ∈ H.bag x) (h ∈ H.hub x), H.agg φ est x h + est x h z

/-- **Lemma V for region bags.** -/
theorem lemmaV (w : V → V → ℝ≥0∞) (ε : ℝ≥0∞) (hε : ε ≠ ∞)
    (lo₁ : ∀ x a h, a ∈ H.bag x → h ∈ H.hub x → distR adj w (H.arc x) a h ≤ est x a h)
    (lo₂ : ∀ x h z, z ∈ H.bag x → h ∈ H.hub x → distR adj w (H.arc x) h z ≤ est x h z)
    (hi₁ : ∀ x a h, a ∈ H.bag x → h ∈ H.hub x →
      est x a h ≤ (1 + ε) * distR adj w (H.arc x) a h)
    (hi₂ : ∀ x h z, z ∈ H.bag x → h ∈ H.hub x →
      est x h z ≤ (1 + ε) * distR adj w (H.arc x) h z)
    (z : V) :
    dsrc adj w φ z ≤ H.query φ est z ∧ H.query φ est z ≤ (1 + ε) * dsrc adj w φ z := by
  constructor
  · simp only [query, agg, ENNReal.iInf_add, le_iInf_iff]
    intro x hz h hh a ha
    calc dsrc adj w φ z ≤ φ a + dist adj w Set.univ a z := iInf_le (fun a => _ + _) a
      _ ≤ φ a + (distR adj w (H.arc x) a h + distR adj w (H.arc x) h z) := by
          gcongr; exact distR_triangle w _ a h z
      _ ≤ φ a + est x a h + est x h z := by
          rw [add_assoc]; gcongr
          · exact lo₁ x a h ha hh
          · exact lo₂ x h z hz hh
  · have hc0 : (1 + ε) ≠ 0 := (lt_of_lt_of_le one_pos le_self_add).ne'
    have hcT : (1 + ε) ≠ ∞ := ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hε⟩
    simp only [dsrc, dist, ENNReal.add_iInf, ENNReal.mul_iInf_of_ne hc0 hcT, le_iInf_iff]
    intro a p _
    obtain ⟨y, h, hh, p₁, p₂, h₁, h₂, ha, -, hz, hw⟩ :=
      H.descend w H.root p (Walk.arcsIn_of_adj H.root_arc p) (H.root_bag a)
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

end RHierarchy

end SsspFlow
