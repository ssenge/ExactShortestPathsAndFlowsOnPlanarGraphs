/-
The arithmetic of notes/MAXFLOW.md, from abstract hypotheses: the filled potentials of one step,
solvability of the portal system, the decay of the remaining value, and the rounding to exact potentials.
Planarity, distances in the dual, labels and rounds are not modelled here.
-/
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace SsspFlow.FlowScaling

/-- Darts with a reversal, faces, and the sign of the darts on the path R. -/
structure Plane (Dart F : Type*) where
  rev : Dart → Dart
  rgt : Dart → F
  σ : Dart → ℤ
  rev_rev : ∀ d, rev (rev d) = d
  σ_rev : ∀ d, σ (rev d) = -σ d

variable {Dart F : Type*} (G : Plane Dart F)

def Plane.lft (d : Dart) : F := G.rgt (G.rev d)

/-- The flow of face potentials plus J units along R. -/
def flow (ϕ : F → ℤ) (J : ℤ) (d : Dart) : ℤ := ϕ (G.lft d) - ϕ (G.rgt d) + G.σ d * J

theorem flow_rev (ϕ : F → ℤ) (J : ℤ) (d : Dart) : flow G ϕ J (G.rev d) = -flow G ϕ J d := by
  simp only [flow, Plane.lft, G.rev_rev, G.σ_rev]
  ring

/-- Part 3 of the Step Lemma: the two residual capacities of an edge sum to K times the old sum. -/
theorem residual_sum (K : ℤ) (C : Dart → ℤ) (ϕ : F → ℤ) (J : ℤ) (d : Dart) :
    (K * C d - flow G ϕ J d) + (K * C (G.rev d) - flow G ϕ J (G.rev d)) = K * (C d + C (G.rev d)) := by
  rw [flow_rev]
  ring

section Fill

variable (P : Finset F) (hP : P.Nonempty)

/-- `ϕ(x) = min over p of ψ(p) + D(p,x)`, where D is K times the distance in Γ. -/
def fill (ψ : F → ℤ) (D : F → F → ℤ) (x : F) : ℤ := P.inf' hP fun p => ψ p + D p x

theorem fill_eq (ψ : F → ℤ) (D : F → F → ℤ) (h0 : ∀ p ∈ P, D p p = 0)
    (hψ : ∀ p ∈ P, ∀ q ∈ P, ψ p ≤ ψ q + D q p) {p : F} (hp : p ∈ P) : fill P hP ψ D p = ψ p := by
  apply le_antisymm
  · have h : fill P hP ψ D p ≤ ψ p + D p p := Finset.inf'_le (fun q => ψ q + D q p) hp
    rw [h0 p hp] at h
    linarith
  · exact Finset.le_inf' _ _ fun q hq => hψ p hp q hq

theorem fill_step (ψ : F → ℤ) (D : F → F → ℤ) (x y : F) (w : ℤ)
    (h : ∀ p ∈ P, D p y ≤ D p x + w) : fill P hP ψ D y ≤ fill P hP ψ D x + w := by
  obtain ⟨p, hp, hpe⟩ := Finset.exists_mem_eq_inf' hP fun p => ψ p + D p x
  have h1 : fill P hP ψ D y ≤ ψ p + D p y := Finset.inf'_le (fun q => ψ q + D q y) hp
  have h2 : fill P hP ψ D x = ψ p + D p x := hpe
  have := h p hp
  linarith

/-- Part 1 of the Step Lemma: the filled potentials give a flow of value J below K·C on every dart. -/
theorem step_feasible (ψ : F → ℤ) (D : F → F → ℤ) (KC : Dart → ℤ) (J : ℤ)
    (h0 : ∀ p ∈ P, D p p = 0) (hψ : ∀ p ∈ P, ∀ q ∈ P, ψ p ≤ ψ q + D q p)
    (hΓ : ∀ d, G.σ d = 0 → ∀ p ∈ P, D p (G.lft d) ≤ D p (G.rgt d) + KC d)
    (hR : ∀ d, G.σ d ≠ 0 → G.rgt d ∈ P ∧ G.lft d ∈ P ∧ ψ (G.lft d) - ψ (G.rgt d) ≤ KC d - G.σ d * J)
    (d : Dart) : flow G (fill P hP ψ D) J d ≤ KC d := by
  unfold flow
  by_cases hs : G.σ d = 0
  · have := fill_step P hP ψ D (G.rgt d) (G.lft d) (KC d) (hΓ d hs)
    rw [hs]
    linarith
  · obtain ⟨h1, h2, h3⟩ := hR d hs
    rw [fill_eq P hP ψ D h0 hψ h1, fill_eq P hP ψ D h0 hψ h2]
    linarith

end Fill

/-- Part 2 of the Step Lemma: if 5J ≤ 36λ then floors of (J/λ)ψ* solve the system, for K = 9, ε = 1/12. -/
theorem system_solvable (P : Set F) (C : Dart → ℤ) (d b : F → F → ℤ) (ψs : F → ℤ) (lam J : ℤ)
    (hlam : 0 < lam) (hJ0 : 0 ≤ J) (hJ : 5 * J ≤ 36 * lam) (hC : ∀ e, 0 ≤ C e)
    (hd : ∀ u ∈ P, ∀ v ∈ P, 0 ≤ d u v) (hb : ∀ u ∈ P, ∀ v ∈ P, 36 * d u v ≤ 5 * b u v)
    (hΓ : ∀ u ∈ P, ∀ v ∈ P, ψs v - ψs u ≤ d u v)
    (hpot : ∀ e, ψs (G.lft e) - ψs (G.rgt e) ≤ C e - G.σ e * lam) :
    (∀ u ∈ P, ∀ v ∈ P, (J * ψs v) / lam - (J * ψs u) / lam ≤ b u v) ∧
      ∀ e, (J * ψs (G.lft e)) / lam - (J * ψs (G.rgt e)) / lam ≤ 9 * C e - G.σ e * J := by
  have key : ∀ x y w : ℤ, x ≤ y + w * lam → x / lam - y / lam ≤ w := by
    intro x y w h
    have h1 : x / lam ≤ (y + w * lam) / lam := Int.ediv_le_ediv hlam h
    rw [Int.add_mul_ediv_right _ _ hlam.ne'] at h1
    linarith
  constructor
  · intro u hu v hv
    apply key
    have h1 := hΓ u hu v hv
    have h2 := hb u hu v hv
    have h3 := hd u hu v hv
    have h4 : J * d u v ≤ b u v * lam := by nlinarith
    nlinarith
  · intro e
    apply key
    have h1 := hpot e
    have h2 := hC e
    have h3 : J ≤ 9 * lam := by linarith
    have h4 : J * C e ≤ 9 * C e * lam := by nlinarith
    nlinarith

/-- One step shrinks what remains: J at least the floor of 36λ/5 gives 5(9λ − J) ≤ 9λ + 4. -/
theorem residual_bound (lam J : ℤ) (h : 36 * lam ≤ 5 * J + 4) : 5 * (9 * lam - J) ≤ 9 * lam + 4 := by
  linarith

/-- The decay of the remaining value, in the integer form that Section 3 uses: p_T / 9^T < (λ+1) / 5^T. -/
theorem scaling_bound (p J : ℕ → ℤ) (hstep : ∀ i, p (i + 1) = 9 * p i - J i)
    (hJ : ∀ i, 36 * p i ≤ 5 * J i + 4) (T : ℕ) :
    5 ^ T * p T + 5 ^ T ≤ 9 ^ T * (p 0 + 1) := by
  induction T with
  | zero => simp
  | succ T ih =>
    have h5 : (0 : ℤ) < 5 ^ T := by positivity
    have h1 : 5 * p (T + 1) ≤ 9 * p T + 4 := by
      rw [hstep]
      exact residual_bound _ _ (hJ T)
    have h2 : 5 ^ T * (5 * p (T + 1)) ≤ 5 ^ T * (9 * p T + 4) :=
      mul_le_mul_of_nonneg_left h1 h5.le
    calc
      (5 : ℤ) ^ (T + 1) * p (T + 1) + 5 ^ (T + 1) = 5 ^ T * (5 * p (T + 1)) + 5 * 5 ^ T := by ring
      _ ≤ 5 ^ T * (9 * p T + 4) + 5 * 5 ^ T := by linarith
      _ = 9 * (5 ^ T * p T + 5 ^ T) := by ring
      _ ≤ 9 * (9 ^ T * (p 0 + 1)) := by linarith
      _ = 9 ^ (T + 1) * (p 0 + 1) := by ring

/-- Invariant (I) of Section 3 for one step. -/
theorem invariant_step (K Sc Δ β ϕd s J C : ℤ) (hC : C = Sc - Δ - s * β) :
    K * C - (ϕd + s * J) = K * Sc - (K * Δ + ϕd) - s * (K * β + J) := by
  subst hC
  ring

/-- Part 2 of the Exactness Lemma. -/
theorem reduced_nonneg (S c s lam β Δ p C : ℤ) (hC : C = S * c - Δ - s * β) (hp : p = S * lam - β)
    (hC0 : 0 ≤ C) (hp0 : 0 ≤ p) (hs : s ≤ 1) : 0 ≤ S * (c - s * lam) - Δ + p := by
  have : S * (c - s * lam) - Δ + p = C + (1 - s) * p := by
    subst hC hp
    ring
  rw [this]
  have : 0 ≤ (1 - s) * p := mul_nonneg (by linarith) hp0
  linarith

/-- The telescoping of Part 3 of the Exactness Lemma. -/
theorem reduced_path (ℓ : Dart → ℤ) (Φ : F → ℤ) (S p : ℤ) :
    ∀ (Q : List Dart) (x y : F), List.IsChain (fun a b => G.lft a = G.rgt b) Q →
      (∀ a ∈ Q.head?, G.rgt a = x) → (∀ a ∈ Q.getLast?, G.lft a = y) → (Q = [] → x = y) →
      (Q.map fun d => S * ℓ d + Φ (G.rgt d) - Φ (G.lft d) + p).sum =
        S * (Q.map ℓ).sum + Φ x - Φ y + p * Q.length := by
  intro Q
  induction Q with
  | nil =>
    intro x y _ _ _ h
    simp [h rfl]
  | cons a Q ih =>
    intro x y hc hx hy _
    have hxa : G.rgt a = x := hx a (by simp)
    cases Q with
    | nil =>
      have hya : G.lft a = y := hy a (by simp)
      subst hxa hya
      simp
    | cons b Q' =>
      have hab : G.lft a = G.rgt b := by
        simpa using (List.isChain_cons_cons.mp hc).1
      have hc' := (List.isChain_cons_cons.mp hc).2
      have := ih (G.rgt b) y hc' (by simp) (by
        intro z hz
        apply hy
        simpa using hz) (by simp)
      simp only [List.map_cons, List.sum_cons, List.length_cons] at this ⊢
      rw [this]
      subst hxa
      rw [hab]
      push_cast
      ring

/-- Part 3 of the Exactness Lemma: dividing a minimum with small perturbations recovers the minimum. -/
theorem floor_of_min {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (L q : ι → ℤ) (S p : ℤ) (hS : 0 < S)
    (hp : ∀ i ∈ s, 0 ≤ p * q i ∧ p * q i < S) :
    (s.inf' hs fun i => S * L i + p * q i) / S = s.inf' hs L := by
  obtain ⟨a, ha, hae⟩ := Finset.exists_mem_eq_inf' hs L
  obtain ⟨b, hb, hbe⟩ := Finset.exists_mem_eq_inf' hs fun i => S * L i + p * q i
  rw [hae, hbe]
  have hLb : L a ≤ L b := by
    rw [← hae]
    exact Finset.inf'_le L hb
  have hval : S * L b + p * q b ≤ S * L a + p * q a := by
    rw [← hbe]
    exact Finset.inf'_le (fun i => S * L i + p * q i) ha
  apply le_antisymm
  · have h1 : S * L b + p * q b < S * (L a + 1) := by
      have := (hp a ha).2
      nlinarith
    have : (S * L b + p * q b) / S < L a + 1 := Int.ediv_lt_of_lt_mul hS (by linarith [h1, mul_comm S (L a + 1)])
    linarith
  · have h2 : S * L a ≤ S * L b + p * q b := by
      have := (hp b hb).1
      nlinarith
    exact (Int.le_ediv_iff_mul_le hS).mpr (by linarith [mul_comm (L a) S])

/-- Part 4 of the Exactness Lemma: distances for c − σλ give a flow of value λ below c. -/
theorem exact_feasible (c : Dart → ℤ) (ψ : F → ℤ) (lam : ℤ)
    (h : ∀ d, ψ (G.lft d) ≤ ψ (G.rgt d) + (c d - G.σ d * lam)) (d : Dart) : flow G ψ lam d ≤ c d := by
  have := h d
  unfold flow
  linarith

end SsspFlow.FlowScaling
