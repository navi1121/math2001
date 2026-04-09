/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.Rel

math2001_init
set_option pp.funBinderTypes true


example (P Q : Prop) : ¬ (P ∧ Q) ↔ (¬ P ∨ ¬ Q) := by
  constructor
  · intro h
    by_cases hP : P
    · right
      intro hQ
      have hPQ : P ∧ Q
      · constructor
        · apply hP
        · apply hQ
      contradiction
    · left
      apply hP
  · sorry

example :
    ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m) ↔ ∃ m : ℤ, m ≠ 2 ∧ ∀ n : ℤ, n ^ 2 ≠ m :=
  calc ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
      ↔ ∃ m : ℤ, ¬(m ≠ 2 → ∃ n : ℤ, n ^ 2 = m) := by rel [not_forall]
    _ ↔ ∃ m : ℤ, m ≠ 2 ∧ ¬(∃ n : ℤ, n ^ 2 = m) := by rel [not_imp]
    _ ↔ ∃ m : ℤ, m ≠ 2 ∧ ∀ n : ℤ, n ^ 2 ≠ m := by rel [not_exists]


example : ¬(∀ n : ℤ, ∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2)
    ↔ ∃ n : ℤ, ∀ m : ℤ, n ^ 2 ≥ m ∨ m ≥ (n + 1) ^ 2 :=
  sorry

#push_neg ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
  -- ∃ m : ℤ, m ≠ 2 ∧ ∀ (n : ℤ), n ^ 2 ≠ m

#push_neg ¬(∀ n : ℤ, ∃ m : ℤ, n ^ 2 < m ∧ m < (n + 1) ^ 2)
  -- ∃ n : ℤ, ∀ m : ℤ, m ≤ n ^ 2 ∨ (n + 1) ^ 2 ≤ m


#push_neg ¬(∃ m n : ℤ, ∀ t : ℝ, m < t ∧ t < n)
#push_neg ¬(∀ a : ℕ, ∃ x y : ℕ, x * y ∣ a → x ∣ a ∧ y ∣ a)
#push_neg ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)


example : ¬ (∃ n : ℕ, n ^ 2 = 2) := by
  push_neg
  intro n
  have hn := le_or_succ_le n 1
  obtain hn | hn := hn
  · apply ne_of_lt
    calc
      n ^ 2 ≤ 1 ^ 2 := by rel [hn]
      _ < 2 := by numbers
  · sorry

/-! # Exercises -/


example (P : Prop) : ¬ (¬ P) ↔ P := by /-solve-/
  constructor
  · intro h
    by_cases hP : P
    · apply hP
    · contradiction
  · intro h
    intro h_not_P
    contradiction

example (P Q : Prop) : ¬ (P → Q) ↔ (P ∧ ¬ Q) := by
  sorry

example (P : α → Prop) : ¬ (∀ x, P x) ↔ ∃ x, ¬ P x := by /-solve-/
  constructor

  -- going to right direction
  · intro h
    by_cases h' : ∃ x, ¬ P x
    · exact h'
    · exfalso
      apply h
      intro x
      by_cases hx : P x
      · exact hx
      · have : ∃ x, ¬ P x := ⟨x, hx⟩
        contradiction

  -- going towards left direction
  · intro h
    obtain ⟨x, h_not_P⟩ := h
    intro h_forall
    have := h_forall x
    exact h_not_P this

example : (¬ ∀ a b : ℤ, a * b = 1 → a = 1 ∨ b = 1)
    ↔ ∃ a b : ℤ, a * b = 1 ∧ a ≠ 1 ∧ b ≠ 1 :=
  sorry

example : (¬ ∃ x : ℝ, ∀ y : ℝ, y ≤ x) ↔ (∀ x : ℝ, ∃ y : ℝ, y > x) := /-solve-/
  have h1 : (¬ ∃ x : ℝ, ∀ y : ℝ, y ≤ x) → (∀ x : ℝ, ∃ y : ℝ, y > x) := by
    intro h
    intro x
    by_contra h'
    have hx : ∀ y : ℝ, y ≤ x := by
      intro y
      by_contra hy
      have hgt : y > x := lt_of_not_ge hy
      apply h'
      exact ⟨y, hgt⟩
    apply h
    exact ⟨x, hx⟩

  have h2 : (∀ x : ℝ, ∃ y : ℝ, y > x) → (¬ ∃ x : ℝ, ∀ y : ℝ, y ≤ x) := by
    intro h
    intro h'
    cases h' with
    | intro x hx =>
      cases h x with
      | intro y hy =>
        have hle : y ≤ x := hx y
        have hnot : ¬ (y > x) := not_lt_of_ge hle
        exact hnot hy

  exact ⟨h1, h2⟩ /-errrorr-/

example : ¬ (∃ m : ℤ, ∀ n : ℤ, m = n + 5) ↔ ∀ m : ℤ, ∃ n : ℤ, m ≠ n + 5 :=
  sorry

#push_neg ¬(∀ n : ℕ, n > 0 → ∃ k l : ℕ, k < n ∧ l < n ∧ k ≠ l)
#push_neg ¬(∀ m : ℤ, m ≠ 2 → ∃ n : ℤ, n ^ 2 = m)
#push_neg ¬(∃ x : ℝ, ∀ y : ℝ, ∃ m : ℤ, x < y * m ∧ y * m < m)
#push_neg ¬(∃ x : ℝ, ∀ q : ℝ, q > x → ∃ m : ℕ, q ^ m > x)


example : ¬ (∀ x : ℝ, x ^ 2 ≥ x) := by /-solve-/
  push_neg
  sorry



example : ¬ (∃ t : ℝ, t ≤ 4 ∧ t ≥ 5) := by
  push_neg
  sorry

example : ¬ Int.Even 7 := by /-solve-/
  dsimp [Int.Even]
  push_neg
  sorry

example {p : ℕ} (k : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hk : k ∣ p) : ¬ Prime p := by
  dsimp [Prime]
  push_neg
  sorry

example : ¬ ∃ a : ℤ, ∀ n : ℤ, 2 * a ^ 3 ≥ n * a + 7 := by /-solve-/
  intro h
  cases h with
  | intro a ha =>
    -- choose a bad n
    let n := 2 * a ^ 3 + 1

    have h1 := ha n
    -- h1 : 2 * a^3 ≥ n * a + 7

    -- expand n
    have h2 : n * a + 7 = (2 * a ^ 3 + 1) * a + 7 := by
      rfl

    -- simplify RHS
    have h3 : (2 * a ^ 3 + 1) * a + 7 = 2 * a ^ 4 + a + 7 := by
      ring

    rw [h2, h3] at h1
 ---finish this proof, then do the next one
    -- now we have:
    -- 2 * a^3 ≥ 2 * a^4 + a + 7

    -- but RHS is strictly bigger → contradiction
    have : 2 * a ^ 4 + a + 7 > 2 * a ^ 3 := by
      -- a^4 dominates a^3, and +a+7 makes it strictly larger
      sorry

    exact not_lt_of_ge h1 this

example {p : ℕ} (hp : ¬ Prime p) (hp2 : 2 ≤ p) : ∃ m, 2 ≤ m ∧ m < p ∧ m ∣ p := by
  have H : ¬ (∀ (m : ℕ), 2 ≤ m → m < p → ¬m ∣ p)
  · intro H
    sorry
  sorry
