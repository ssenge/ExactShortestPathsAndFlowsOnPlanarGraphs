import SsspFlow.LemmaD
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Round
import Mathlib.Tactic.LinearCombination

/-!
# Algorithm 1 of [3] with the discretization fix

Assembly of Theorem A in `sssp_flow/NOTES.md`. [3, App. C.1] calls the oracle on `ℓ_i + η`
(`η = 1/poly`) but applies the Algorithm 1 update to `ℓ_i`. An answer that meets the oracle
contract for `ℓ_i + η` can then push an arc to `-η` (`c1_negative`). The fix uses `ℓ_i + η` as
the base of the update: for an arc `(a, b)`,
  `ℓ_{i+1} = ℓ_i + η - d_i(b)/α + d_i(a)/α`.

`Run` records one run. The oracle contract is: `d_i(s) = 0`; `d_i` never underestimates
`dist_{ℓ_i + η}(s, ·)`; and `d_i(b) - d_i(a) ≤ α·(ℓ_i + η)` on every arc, which smoothness w.r.t.
`ℓ_i + η` implies. With `n = |V|`, `q = 1 - 1/α` and `D_i = dist_{ℓ_i}(s, ·)`:
* `len_nonneg`: every `ℓ_i ≥ 0`, so the oracle always sees lengths `≥ η`;
* `contract`: `D_{i+1}(u) ≤ q·D_i(u) + (n-1)η` at every vertex;
* `exact`: for integer `ℓ`, if `q^I·D_0(u) + α(n-1)η < 1/2` and `I(n-1)η < 1/2`, then rounding
  `Σ_{i<I} d_i(u)/α` gives `D_0(u)` exactly.

`η = 0` is [3, Lemma 3.1] itself. Every vertex is assumed reachable from `s`; in Theorem A the
offset `M₁` arranges this.

## Not formalized
The oracle (Algorithm 3 of [3] and the labels), the choice `I = O(α log(nΔ))`, the aspect-ratio
and integer rescaling inside the oracle, and the round count.
-/

namespace SsspFlow.Boost

open SsspFlow.FaceDisjoint (Walk)

universe u

variable {V : Type u} {E : V → V → Type u}

/-- `dist_ℓ(s, u)`: the infimum of walk lengths. -/
noncomputable def dist (s : V) (ℓ : ∀ a b, E a b → ℝ) (u : V) : ℝ := ⨅ p : Walk E s u, p.wt ℓ

lemma wt_nonneg (ℓ : ∀ a b, E a b → ℝ) (h : ∀ a b e, 0 ≤ ℓ a b e) :
    ∀ {a b : V} (p : Walk E a b), 0 ≤ p.wt ℓ
  | _, _, .nil _ => by simp
  | _, _, .cons e p => by rw [Walk.wt_cons]; exact add_nonneg (h _ _ e) (wt_nonneg ℓ h p)

/-- Changing each arc `(a, b)` by `η - f b + f a` changes a walk by `len·η - f(end) + f(start)`. -/
lemma wt_shift (ℓ ℓ' : ∀ a b, E a b → ℝ) (η : ℝ) (f : V → ℝ)
    (h : ∀ a b e, ℓ' a b e = ℓ a b e + η - f b + f a) :
    ∀ {a b : V} (p : Walk E a b), p.wt ℓ' = p.wt ℓ + p.len * η - f b + f a
  | _, _, .nil _ => by simp
  | _, _, .cons e p => by
    rw [Walk.wt_cons, Walk.wt_cons, wt_shift ℓ ℓ' η f h p, h, Walk.len_cons]; push_cast; ring

lemma dist_le {s u : V} (ℓ : ∀ a b, E a b → ℝ) (h : ∀ a b e, 0 ≤ ℓ a b e) (p : Walk E s u) :
    dist s ℓ u ≤ p.wt ℓ :=
  ciInf_le ⟨0, by rintro _ ⟨q, rfl⟩; exact wt_nonneg ℓ h q⟩ p

lemma le_dist {s u : V} (ℓ : ∀ a b, E a b → ℝ) [Nonempty (Walk E s u)] {c : ℝ}
    (h : ∀ p : Walk E s u, c ≤ p.wt ℓ) : c ≤ dist s ℓ u :=
  le_ciInf h

/-- Why the base must be `ℓ_i + η`. One arc `s → v` of length `0`, answer `d(s) = 0`,
`d(v) = α·η`: it is smooth and noncontractive for `ℓ + η = η`, yet the update with base `ℓ`
gives `-η`. -/
lemma c1_negative (α η : ℝ) (hα : 1 ≤ α) (hη : 0 < η) :
    α * η - 0 ≤ α * (0 + η) ∧ 0 + η ≤ α * η ∧ 0 - α * η / α + 0 / α = -η := by
  have : α ≠ 0 := by positivity
  refine ⟨by linarith, by nlinarith, by field_simp; ring⟩

/-- One run of Algorithm 1 with base `ℓ_i + η`: input lengths `ℓ`, current lengths `L i`, and
oracle answers `dt i` meeting the contract for `L i + η`. -/
structure Run (s : V) (ℓ : ∀ a b, E a b → ℕ) (L : ℕ → ∀ a b, E a b → ℝ) (dt : ℕ → V → ℝ)
    (α η : ℝ) : Prop where
  one_le : 1 ≤ α
  eta_nonneg : 0 ≤ η
  reach : ∀ u, Nonempty (Walk E s u)
  init : ∀ a b e, L 0 a b e = ℓ a b e
  step : ∀ i a b e, L (i + 1) a b e = L i a b e + η - dt i b / α + dt i a / α
  src : ∀ i, dt i s = 0
  nc : ∀ i u, dist s (fun a b e => L i a b e + η) u ≤ dt i u
  smooth : ∀ i a b (e : E a b), dt i b - dt i a ≤ α * (L i a b e + η)

namespace Run

variable {s : V} {ℓ : ∀ a b, E a b → ℕ} {L : ℕ → ∀ a b, E a b → ℝ} {dt : ℕ → V → ℝ} {α η : ℝ}
  (R : Run s ℓ L dt α η)
include R

lemma alpha_pos : 0 < α := by linarith [R.one_le]

/-- Lengths stay nonnegative, so the oracle only sees lengths `≥ η`. -/
lemma len_nonneg : ∀ i a b (e : E a b), 0 ≤ L i a b e
  | 0, a, b, e => by rw [R.init]; positivity
  | i + 1, a, b, e => by
    rw [R.step]
    have h := R.smooth i a b e
    have : dt i b / α - dt i a / α ≤ L i a b e + η := by
      rw [← sub_div, div_le_iff₀ R.alpha_pos]; linarith
    linarith

lemma shift (i : ℕ) {a b : V} (p : Walk E a b) :
    p.wt (L (i + 1)) = p.wt (L i) + p.len * η - dt i b / α + dt i a / α :=
  wt_shift (L i) (L (i + 1)) η (fun v => dt i v / α) (R.step i) p

lemma dist_nonneg (i : ℕ) (u : V) : 0 ≤ dist s (L i) u := by
  have := R.reach u
  exact le_dist _ fun p => wt_nonneg _ (R.len_nonneg i) p

/-- The oracle answer bounds the current distance from above. -/
lemma dist_le_dt (i : ℕ) (u : V) : dist s (L i) u ≤ dt i u := by
  have := R.reach u
  refine le_trans (le_dist _ fun p => ?_) (R.nc i u)
  have h1 := wt_shift (L i) (fun a b e => L i a b e + η) η (fun _ => 0) (by intros; ring) p
  have h2 := dist_le (L i) (R.len_nonneg i) p
  have h3 : 0 ≤ (p.len : ℝ) * η := mul_nonneg (Nat.cast_nonneg _) R.eta_nonneg
  linarith

lemma step_lower (i : ℕ) (u : V) : dist s (L i) u - dt i u / α ≤ dist s (L (i + 1)) u := by
  have := R.reach u
  refine le_dist _ fun p => ?_
  have h1 := R.shift i p
  rw [R.src, zero_div] at h1
  have h2 := dist_le (L i) (R.len_nonneg i) p
  have h3 : 0 ≤ (p.len : ℝ) * η := mul_nonneg (Nat.cast_nonneg _) R.eta_nonneg
  linarith

variable [Fintype V]

lemma step_upper (i : ℕ) (u : V) :
    dist s (L (i + 1)) u + dt i u / α ≤ dist s (L i) u + (Fintype.card V - 1) * η := by
  have := R.reach u
  have key : ∀ p : Walk E s u,
      dist s (L (i + 1)) u + dt i u / α - (Fintype.card V - 1) * η ≤ p.wt (L i) := by
    intro p
    obtain ⟨q, hq, hw⟩ :=
      Walk.short (L i) (fun _ c => wt_nonneg _ (R.len_nonneg i) c) _ p rfl
    have h1 := R.shift i q
    rw [R.src, zero_div] at h1
    have h2 := dist_le (L (i + 1)) (R.len_nonneg (i + 1)) q
    have h3 : (q.len : ℝ) + 1 ≤ Fintype.card V := by exact_mod_cast hq
    have h4 : (q.len : ℝ) * η ≤ (Fintype.card V - 1) * η :=
      mul_le_mul_of_nonneg_right (by linarith) R.eta_nonneg
    linarith
  have := le_dist (L i) key
  linarith

/-- Per-vertex contraction by `1 - 1/α`, up to the `η` error. -/
lemma contract (i : ℕ) (u : V) :
    dist s (L (i + 1)) u ≤ (1 - 1 / α) * dist s (L i) u + (Fintype.card V - 1) * η := by
  have h1 := R.step_upper i u
  have := R.alpha_pos.le
  have h2 : dist s (L i) u / α ≤ dt i u / α := by gcongr; exact R.dist_le_dt i u
  have : (1 - 1 / α) * dist s (L i) u = dist s (L i) u - dist s (L i) u / α := by ring
  linarith

lemma decay (u : V) : ∀ i, dist s (L i) u ≤
    (1 - 1 / α) ^ i * dist s (L 0) u + α * (Fintype.card V - 1) * η
  | 0 => by
    have : Nonempty V := ⟨u⟩
    have : (1 : ℝ) ≤ Fintype.card V := Nat.one_le_cast.2 Fintype.card_pos
    have : 0 ≤ α * (Fintype.card V - 1) * η :=
      mul_nonneg (mul_nonneg R.alpha_pos.le (by linarith)) R.eta_nonneg
    rw [pow_zero, one_mul]; linarith
  | i + 1 => by
    have hq : 0 ≤ 1 - 1 / α := by rw [sub_nonneg, div_le_one R.alpha_pos]; exact R.one_le
    have : α ≠ 0 := R.alpha_pos.ne'
    calc dist s (L (i + 1)) u
        ≤ (1 - 1 / α) * dist s (L i) u + (Fintype.card V - 1) * η := R.contract i u
      _ ≤ (1 - 1 / α) * ((1 - 1 / α) ^ i * dist s (L 0) u + α * (Fintype.card V - 1) * η) +
          (Fintype.card V - 1) * η := by gcongr; exact decay u i
      _ = (1 - 1 / α) ^ (i + 1) * dist s (L 0) u + α * (Fintype.card V - 1) * η := by
          have h : (1 - 1 / α) * α = α - 1 := by
            rw [sub_mul, one_div, inv_mul_cancel₀ this, one_mul]
          rw [pow_succ]; linear_combination (Fintype.card V - 1) * η * h

/-- The estimates telescope: their sum is `D_0 - D_I` up to `I(n-1)η`. -/
lemma sum_bounds (u : V) : ∀ I : ℕ,
    dist s (L 0) u - dist s (L I) u ≤ ∑ i ∈ Finset.range I, dt i u / α ∧
      ∑ i ∈ Finset.range I, dt i u / α ≤
        dist s (L 0) u - dist s (L I) u + I * (Fintype.card V - 1) * η
  | 0 => by simp
  | I + 1 => by
    obtain ⟨h1, h2⟩ := sum_bounds u I
    have l := R.step_lower I u
    have up := R.step_upper I u
    rw [Finset.sum_range_succ]; push_cast
    constructor <;> linarith

omit [Fintype V] in
/-- With integer input lengths the distance is an integer. -/
lemma dist_nat (u : V) : ∃ k : ℕ, dist s (L 0) u = k := by
  classical
  have hw : ∀ {a b : V} (p : Walk E a b), ∃ k : ℕ, p.wt (L 0) = k := by
    intro a b p
    induction p with
    | nil a => exact ⟨0, by simp⟩
    | cons e p ih =>
      obtain ⟨k, hk⟩ := ih
      exact ⟨ℓ _ _ e + k, by simp [hk, R.init]⟩
  have hex : ∃ k : ℕ, ∃ p : Walk E s u, p.wt (L 0) = k := by
    obtain ⟨p⟩ := R.reach u
    obtain ⟨k, hk⟩ := hw p
    exact ⟨k, p, hk⟩
  obtain ⟨p₀, hp₀⟩ := Nat.find_spec hex
  refine ⟨Nat.find hex, le_antisymm ((dist_le _ (R.len_nonneg 0) p₀).trans hp₀.le) ?_⟩
  have := R.reach u
  refine le_dist _ fun p => ?_
  obtain ⟨k, hk⟩ := hw p
  rw [hk]; exact_mod_cast Nat.find_min' hex ⟨p, hk⟩

/-- **Exactness.** Rounding the summed estimates gives the exact distance. -/
theorem exact (I : ℕ) (u : V)
    (hI : (1 - 1 / α) ^ I * dist s (L 0) u + α * (Fintype.card V - 1) * η < 1 / 2)
    (hIη : I * (Fintype.card V - 1) * η < 1 / 2) :
    (round (∑ i ∈ Finset.range I, dt i u / α) : ℝ) = dist s (L 0) u := by
  obtain ⟨k, hk⟩ := R.dist_nat u
  obtain ⟨h1, h2⟩ := R.sum_bounds u I
  have h3 := R.decay u I
  have h4 := R.dist_nonneg I u
  rw [hk] at h1 h2 h3 hI ⊢
  have : round (∑ i ∈ Finset.range I, dt i u / α) = (k : ℤ) := by
    rw [round_eq, Int.floor_eq_iff]; push_cast; constructor <;> linarith
  rw [this]; simp

end Run

end SsspFlow.Boost
