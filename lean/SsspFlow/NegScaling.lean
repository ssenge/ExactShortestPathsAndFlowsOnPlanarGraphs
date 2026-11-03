import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Elementary core of `notes/NEGATIVE.md`

Integer weights. Division is floor division, since the divisor is positive.

* Scaling Lemma: `round_low`, `round_back`, `round_cycle`, `bound_drops`, `hop_recover`.
* Lemma 1, few negative arcs by alternation: `alt_bound`.
* Lemma 3, a shortest path inside a cluster: `short_in_cluster`.
* The arithmetic of step B in the restricted algorithm: `forward_arc`.
-/

namespace SsspFlow.NegScaling

/-- A rounded weight stays at least `-1`. -/
theorem round_low {x B ρ α : ℤ} (hρ : 0 < ρ) (hx : -B ≤ x) (hB : B ≤ ρ * (α + 1)) : -1 ≤ x / ρ + α := by
  have : -(α + 1) ≤ x / ρ := by
    rw [Int.le_ediv_iff_mul_le hρ]
    nlinarith
  linarith

/-- A potential for the rounded weight gives the new lower bound `-ρ α`. -/
theorem round_back {x ρ α a b : ℤ} (hρ : 0 < ρ) (h : 0 ≤ x / ρ + α + a - b) : -(ρ * α) ≤ x + ρ * a - ρ * b := by
  have h₁ : ρ * (x / ρ) ≤ x := Int.mul_ediv_self_le hρ.ne'
  nlinarith

theorem lt_round {x ρ : ℤ} (hρ : 0 < ρ) : x < ρ * (x / ρ + 1) := by
  have := Int.lt_mul_ediv_self_add (x := x) hρ
  linarith [this, mul_add ρ (x / ρ) 1]

/-- Rounded cycles keep mean at least one, for each pair `(ρ, α)` used in the lemma. -/
theorem round_cycle {ι : Type*} (C : Finset ι) (x : ι → ℤ) {ρ α L : ℤ} (hρ : 0 < ρ) (hL : L ≤ ∑ i ∈ C, x i)
    (hmean : ρ * ((2 - α) * (C.card : ℤ)) ≤ L) : (C.card : ℤ) ≤ ∑ i ∈ C, (x i / ρ + α) := by
  have h₁ : ∑ i ∈ C, x i ≤ ρ * ∑ i ∈ C, (x i / ρ + 1) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => (lt_round hρ).le
  have h₂ : ∑ i ∈ C, (x i / ρ + α) = ∑ i ∈ C, (x i / ρ + 1) + (α - 1) * (C.card : ℤ) := by
    have : ∀ i ∈ C, x i / ρ + α = (x i / ρ + 1) + (α - 1) := fun i _ => by ring
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    ring
  have h₃ : (2 - α) * (C.card : ℤ) ≤ ∑ i ∈ C, (x i / ρ + 1) := by
    have : ρ * ((2 - α) * (C.card : ℤ)) ≤ ρ * ∑ i ∈ C, (x i / ρ + 1) := by linarith
    exact le_of_mul_le_mul_left this hρ
  rw [h₂]
  nlinarith

/-- The bound `B` drops in the phases with `α = 2`. -/
theorem bound_drops {B : ℤ} (h : 5 ≤ B) : 2 * ((B + 2) / 3) < B := by
  omega

theorem low_phase {B : ℤ} (_h : 5 ≤ B) : B ≤ (B + 2) / 3 * (2 + 1) := by
  omega

/-- Distances in `w` come back from `x = 2((n + 1) w + 1)` by floor division. -/
theorem hop_recover {w h n : ℤ} (h₀ : 0 ≤ h) (h₁ : h < n + 1) : (2 * (n + 1) * w + 2 * h) / (2 * (n + 1)) = w := by
  have hn : 0 < 2 * (n + 1) := by linarith
  rw [Int.ediv_eq_iff_of_pos hn]
  constructor <;> nlinarith

/-- Cycles of `x = 2((n + 1) w + 1)`: positive with mean two if `w(C) ≥ 0`, negative if `w(C) < 0` and `|C| ≤ n`. -/
theorem cycle_up {wC c n : ℤ} (hw : 0 ≤ wC) (hn : 0 ≤ n) : 2 * c ≤ 2 * ((n + 1) * wC + c) := by
  nlinarith

theorem cycle_neg {wC c n : ℤ} (hw : wC < 0) (hc : c ≤ n) (hn : 0 ≤ n) : 2 * ((n + 1) * wC + c) < 0 := by
  nlinarith

/-! ### Lemma 1 -/

section Alternation

variable {V : Type*} (Pos Neg : V → V → Prop) (wp : V → V → ℤ) (φ : V → ℤ)

/-- A walk from `x` to `v` with `k` negative arcs and reduced length `a`. -/
inductive Walk (x : V) : V → ℕ → ℤ → Prop
  | nil : Walk x x 0 0
  | pos {u v k a} : Walk x u k a → Pos u v → Walk x v k (a + wp u v)
  | neg {u v k a} : Walk x u k a → Neg u v → Walk x v (k + 1) (a + wp u v)

/-- What the alternation computes: `A 0` from the offsets, then the arcs of each kind.
Each `A (i + 1)` is the oracle run from the relaxation of `A i`, so it is at most `A i`. -/
structure Alt (A : ℕ → V → ℤ) : Prop where
  init : ∀ x, A 0 x ≤ -φ x
  pos : ∀ i u v, Pos u v → A i v ≤ A i u + wp u v
  neg : ∀ i u v, Neg u v → A (i + 1) v ≤ A i u + wp u v
  mono : ∀ i v, A (i + 1) v ≤ A i v

variable {Pos Neg wp φ}

theorem alt_mono {A : ℕ → V → ℤ} (h : Alt Pos Neg wp φ A) {i j : ℕ} (hij : i ≤ j) (v : V) : A j v ≤ A i v := by
  induction hij with
  | refl => exact le_refl _
  | step _ ih => exact (h.mono _ v).trans ih

/-- Every walk with `k` negative arcs is seen by `A k`. -/
theorem alt_walk {A : ℕ → V → ℤ} (h : Alt Pos Neg wp φ A) {x v : V} {k : ℕ} {a : ℤ} (P : Walk Pos Neg wp x v k a) :
    A k v ≤ -φ x + a := by
  induction P with
  | nil => simpa using h.init x
  | @pos u v k a _ hp ih => have := h.pos k u v hp; linarith
  | @neg u v k a _ hn ih => have := h.neg k u v hn; linarith

/-- The statement of Lemma 1: if the reduced length of the walk is `a = w(P) + φ x - φ v`, then
`A t v + φ v ≤ w(P)` for each walk with at most `t` negative arcs. -/
theorem alt_bound {A : ℕ → V → ℤ} (h : Alt Pos Neg wp φ A) {x v : V} {k t : ℕ} {a wP : ℤ} (P : Walk Pos Neg wp x v k a)
    (hk : k ≤ t) (ha : a = wP + φ x - φ v) : A t v + φ v ≤ wP := by
  have h₁ := alt_walk h P
  have h₂ := alt_mono h hk v
  linarith

end Alternation

/-! ### Lemma 3 -/

section Short

variable {E : Type*} (w : E → ℤ)

/-- `max(w, 0)`, the weight in the graph with negative weights rounded up. -/
def wpos (e : E) : ℤ := max (w e) 0

theorem sum_wpos_le (P : List E) (h : ∀ e ∈ P, -1 ≤ w e) : (P.map (wpos w)).sum ≤ (P.map w).sum + (P.length : ℤ) := by
  induction P with
  | nil => simp
  | cons e P ih =>
    have he := h e (by simp)
    have := ih fun e' he' => h e' (by simp [he'])
    have h₁ : wpos w e ≤ w e + 1 := by
      unfold wpos
      exact max_le (by linarith) (by linarith)
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    push_cast
    linarith

theorem sum_le_wpos (Q : List E) : (Q.map w).sum ≤ (Q.map (wpos w)).sum := by
  induction Q with
  | nil => simp
  | cons e Q ih =>
    simp only [List.map_cons, List.sum_cons]
    have : w e ≤ wpos w e := le_max_left _ _
    linarith

/-- A shortest path `P` from the cluster to `v` has weight at most zero. `Q` is a path of the rounded graph back,
in the whole graph, of rounded weight at most `d`, the weak diameter of the cluster. Restricted means that the closed walk
has weight at least its length. Then `P` has at most `d` arcs and rounded weight at most `d`. -/
theorem short_in_cluster (P Q : List E) {d : ℤ} (hlow : ∀ e ∈ P, -1 ≤ w e) (hP : (P.map w).sum ≤ 0)
    (hQ : (Q.map (wpos w)).sum ≤ d) (hC : ((P.length + Q.length : ℕ) : ℤ) ≤ (P.map w).sum + (Q.map w).sum) :
    (P.length : ℤ) ≤ d ∧ (P.map (wpos w)).sum ≤ d := by
  have h₁ := sum_wpos_le w P hlow
  have h₂ := sum_le_wpos w Q
  have h₃ : (0 : ℤ) ≤ (Q.length : ℤ) := by positivity
  push_cast at hC
  constructor <;> linarith

end Short

/-! ### Step B -/

/-- An arc from a lower cluster to a higher one is nonnegative after the shift by `-i n`. -/
theorem forward_arc {w a b n i j : ℤ} (hw : -1 ≤ w) (ha : -(n - 1) ≤ a) (hb : b ≤ 0) (hn : 0 ≤ n) (hij : i < j) :
    0 ≤ w + (a - i * n) - (b - j * n) := by
  have : n ≤ (j - i) * n := by nlinarith
  linarith

end SsspFlow.NegScaling
