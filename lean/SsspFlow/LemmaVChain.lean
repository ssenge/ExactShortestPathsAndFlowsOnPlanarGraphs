import SsspFlow.LemmaVRegion

/-!
# Lemma V for labels along a chain

The form of Lemma V that matches distance labels. A vertex holds estimates only for the bags on
its chain: the root, and from a bag on the chain in which it is no hub, the child that contains
it. So the chain stops at the first bag in which the vertex is a hub. The estimates may
approximate distances in the whole graph or distances in the bag: only the lower bound by
`dist_G` and the upper bound by `(1 + ε) · dist_X` are used.

Bags carry arc sets as in `RHierarchy`; induced bags are the case
`arc x a b ↔ a ∈ bag x ∧ b ∈ bag x`.

`lemmaV_chain` proves `d(σ, v) ≤ queryC v ≤ (1 + ε) · d(σ, v)`.
-/

open scoped ENNReal

namespace SsspFlow

universe u v

namespace RHierarchy

variable {V : Type u} {ι : Type v} {adj : V → V → Prop}

/-- The bag `x` lies on the chain of `z`. -/
inductive Chain (H : RHierarchy V ι adj) (z : V) : ι → Prop
  | root : Chain H z H.root
  | step {x c : ι} : Chain H z x → z ∉ H.hub x → H.kid c x → z ∈ H.bag c → Chain H z c

variable (H : RHierarchy V ι adj)

lemma Chain.mem {z : V} {x : ι} (hc : H.Chain z x) : z ∈ H.bag x := by
  cases hc with
  | root => exact H.root_bag z
  | step _ _ _ hz => exact hz

/-- Descend from a bag on the chains of both ends until a hub lies on the walk. -/
lemma descendChain (w : V → V → ℝ≥0∞) (x : ι) {a b : V} (p : Walk adj a b)
    (hA : p.arcsIn (H.arc x)) (hca : H.Chain a x) (hcb : H.Chain b x) :
    ∃ y h, h ∈ H.hub y ∧ H.Chain a y ∧ H.Chain b y ∧
      ∃ (p₁ : Walk adj a h) (p₂ : Walk adj h b), p₁.arcsIn (H.arc y) ∧ p₂.arcsIn (H.arc y) ∧
        p₁.wt w + p₂.wt w = p.wt w := by
  induction x using H.wf.induction generalizing a b with
  | _ x ih =>
  by_cases hh : ∃ h ∈ p.support, h ∈ H.hub x
  · obtain ⟨h, hp, hh⟩ := hh
    obtain ⟨p₁, p₂, h₁, h₂, hw⟩ := p.splitA w (H.arc x) hA hp
    exact ⟨x, h, hh, hca, hcb, p₁, p₂, h₁, h₂, hw⟩
  · push Not at hh
    obtain ⟨c, hc, hp, hac⟩ := H.one_kid x p hA (Chain.mem H hca) hh
    have hbc : b ∈ H.bag c := Walk.support_sub (H.arc_bag c) p hp hac b p.end_mem
    exact ih c hc p hp (hca.step (hh a p.start_mem) hc hac) (hcb.step (hh b p.end_mem) hc hbc)

variable (φ : V → ℝ≥0∞) (est : ι → V → V → ℝ≥0∞)

/-- `A_x(h)`: the minimum over the vertices with `x` on their chain. -/
noncomputable def aggC (x : ι) (h : V) : ℝ≥0∞ := ⨅ (a : V) (_ : H.Chain a x), φ a + est x a h

/-- The query of Lemma V over the chain of `z`. -/
noncomputable def queryC (z : V) : ℝ≥0∞ :=
  ⨅ (x : ι) (_ : H.Chain z x) (h ∈ H.hub x), H.aggC φ est x h + est x h z

/-- **Lemma V for labels along a chain.** -/
theorem lemmaV_chain (w : V → V → ℝ≥0∞) (ε : ℝ≥0∞) (hε : ε ≠ ∞)
    (lo₁ : ∀ x a h, H.Chain a x → h ∈ H.hub x → dist adj w Set.univ a h ≤ est x a h)
    (lo₂ : ∀ x h z, H.Chain z x → h ∈ H.hub x → dist adj w Set.univ h z ≤ est x h z)
    (hi₁ : ∀ x a h, H.Chain a x → h ∈ H.hub x →
      est x a h ≤ (1 + ε) * distR adj w (H.arc x) a h)
    (hi₂ : ∀ x h z, H.Chain z x → h ∈ H.hub x →
      est x h z ≤ (1 + ε) * distR adj w (H.arc x) h z)
    (z : V) :
    dsrc adj w φ z ≤ H.queryC φ est z ∧ H.queryC φ est z ≤ (1 + ε) * dsrc adj w φ z := by
  constructor
  · simp only [queryC, aggC, ENNReal.iInf_add, le_iInf_iff]
    intro x hz h hh a ha
    calc dsrc adj w φ z ≤ φ a + dist adj w Set.univ a z := iInf_le (fun a => _ + _) a
      _ ≤ φ a + (dist adj w Set.univ a h + dist adj w Set.univ h z) := by
          gcongr; exact dist_triangle w _ a h z
      _ ≤ φ a + est x a h + est x h z := by
          rw [add_assoc]; gcongr
          · exact lo₁ x a h ha hh
          · exact lo₂ x h z hz hh
  · have hc0 : (1 + ε) ≠ 0 := (lt_of_lt_of_le one_pos le_self_add).ne'
    have hcT : (1 + ε) ≠ ∞ := ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hε⟩
    simp only [dsrc, dist, ENNReal.add_iInf, ENNReal.mul_iInf_of_ne hc0 hcT, le_iInf_iff]
    intro a p _
    obtain ⟨y, h, hh, ha, hz, p₁, p₂, h₁, h₂, hw⟩ :=
      H.descendChain w H.root p (Walk.arcsIn_of_adj H.root_arc p) Chain.root Chain.root
    calc H.queryC φ est z ≤ H.aggC φ est y h + est y h z :=
          (iInf₂_le y hz).trans (iInf₂_le h hh)
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
