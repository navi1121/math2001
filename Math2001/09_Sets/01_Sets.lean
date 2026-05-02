/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init

open Set


#check {n : ℤ | n ≤ 3}


example : 1 ∈ {n : ℤ | n ≤ 3} := by
  dsimp
  numbers


namespace Nat
example : 10 ∉ {n : ℕ | Odd n} := by
  dsimp
  rw [← even_iff_not_odd]
  use 5
  numbers
end Nat


example : {a : ℕ | 4 ∣ a} ⊆ {b : ℕ | 2 ∣ b} := by
  dsimp [Set.subset_def] -- optional
  intro a ha
  obtain ⟨k, hk⟩ := ha
  use 2 * k
  calc a = 4 * k := hk
    _ = 2 * (2 * k) := by ring


example : {x : ℝ | 0 ≤ x ^ 2} ⊈ {t : ℝ | 0 ≤ t} := by
  dsimp [Set.subset_def]
  push_neg
  use -3
  constructor
  · numbers
  · numbers


example : {x : ℤ | Int.Odd x} = {a : ℤ | ∃ k, a = 2 * k - 1} := by
  ext x
  dsimp
  constructor
  · intro h
    obtain ⟨l, hl⟩ := h
    use l + 1
    calc x = 2 * l + 1 := by rw [hl]
      _ = 2 * (l + 1) - 1 := by ring
  · intro h
    obtain ⟨k, hk⟩ := h
    use k - 1
    calc x = 2 * k - 1 := by rw [hk]
      _ = 2 * (k - 1) + 1 := by ring


example : {a : ℕ | 4 ∣ a} ≠ {b : ℕ | 2 ∣ b} := by
  ext
  dsimp
  push_neg
  use 6
  right
  constructor
  · apply Nat.not_dvd_of_exists_lt_and_lt
    use 1
    constructor <;> numbers
  · use 3
    numbers


example : {k : ℤ | 8 ∣ 5 * k} = {l : ℤ | 8 ∣ l} := by
  ext n
  dsimp
  constructor
  · intro hn
    obtain ⟨a, ha⟩ := hn
    use -3 * a + 2 * n
    calc
      n = -3 * (5 * n) + 16 * n := by ring
      _ = -3 * (8 * a) + 16 * n := by rw [ha]
      _ = 8 * (-3 * a + 2 * n) := by ring
  · intro hn
    obtain ⟨a, ha⟩ := hn
    use 5 * a
    calc 5 * n = 5 * (8 * a) := by rw [ha]
      _ = 8 * (5 * a) := by ring


example : {x : ℝ | x ^ 2 - x - 2 = 0} = {-1, 2} := by
  ext x
  dsimp
  constructor
  · intro h
    have hx :=
    calc
      (x + 1) * (x - 2) = x ^ 2 - x - 2 := by ring
        _ = 0 := by rw [h]
    rw [mul_eq_zero] at hx
    obtain hx | hx := hx
    · left
      addarith [hx]
    · right
      addarith [hx]
  · intro h
    obtain h | h := h
    · calc x ^ 2 - x - 2 = (-1) ^ 2 - (-1) - 2 := by rw [h]
        _ = 0 := by numbers
    · calc x ^ 2 - x - 2 = 2 ^ 2 - 2 - 2 := by rw [h]
        _ = 0 := by numbers


example : {1, 3, 6} ⊆ {t : ℚ | t < 10} := by
  dsimp [Set.subset_def]
  intro t ht
  obtain h1 | h3 | h6 := ht
  · addarith [h1]
  · addarith [h3]
  · addarith [h6]

/-! # Exercises -/


example : 4 ∉ {a : ℚ | a < 3} := by -- complete this
  dsimp
  numbers

example : 4 ∉ {a : ℚ | a < 3} := by
  sorry

example : 6 ∈ {n : ℕ | n ∣ 42} := by -- complete this
  dsimp
  use 7
  numbers

example : 6 ∉ {n : ℕ | n ∣ 42} := by
  sorry


example : 8 ∉ {k : ℤ | 5 ∣ k} := by -- complete this
  dsimp
  apply Int.not_dvd_of_exists_lt_and_lt 8 5
  use 1
  constructor <;> numbers

example : 8 ∉ {k : ℤ | 5 ∣ k} := by
  sorry

example : 11 ∈ {n : ℕ | Odd n} := by -- complete this
  dsimp
  use 5
  numbers

example : 11 ∉ {n : ℕ | Odd n} := by
  sorry


example : -3 ∈ {x : ℝ | ∀ y : ℝ, x ≤ y ^ 2} := by -- complete this
  dsimp
  intro y
  calc (-3 : ℝ) ≤ 0 := by numbers
    _ ≤ y ^ 2 := by positivity

example : -3 ∉ {x : ℝ | ∀ y : ℝ, x ≤ y ^ 2} := by
  sorry


example : {a : ℕ | 20 ∣ a} ⊆ {x : ℕ | 5 ∣ x} := by -- complete this
  dsimp [Set.subset_def]
  intro a ha
  obtain ⟨k, hk⟩ := ha
  use 4 * k
  calc a = 20 * k := hk
    _ = 5 * (4 * k) := by ring

example : {a : ℕ | 20 ∣ a} ⊈ {x : ℕ | 5 ∣ x} := by
  sorry


example : {a : ℕ | 5 ∣ a} ⊈ {x : ℕ | 20 ∣ x} := by -- complete this
  dsimp [Set.subset_def]
  push_neg
  use 5
  constructor
  · use 1
    numbers
  · intro h
    obtain ⟨k, hk⟩ := h
    have hk1 : k < 1 := by
      by_contra hk1
      have hkge : k ≥ 1 := by exact Nat.not_lt.mp hk1
      have hbig : 20 * k ≥ 20 := by
        calc
          20 * k ≥ 20 * 1 := by rel [hkge]
          _ = 20 := by ring
      rw [← hk] at hbig
      numbers at hbig
    interval_cases k
    numbers at hk

example : {a : ℕ | 5 ∣ a} ⊈ {x : ℕ | 20 ∣ x} := by
  sorry

example : {r : ℤ | 3 ∣ r} ⊈ {s : ℤ | 0 ≤ s} := by -- complete this
  dsimp [Set.subset_def]
  push_neg
  use -3
  constructor
  · use -1
    numbers
  · numbers

example : {r : ℤ | 3 ∣ r} ⊈ {s : ℤ | 0 ≤ s} := by
  sorry

example : {m : ℤ | m ≥ 10} ⊆ {n : ℤ | n ^ 3 - 7 * n ^ 2 ≥ 4 * n} := by -- complete this
  dsimp [Set.subset_def]
  intro n hn
  have h1 : 0 ≤ n - 10 := by addarith [hn]
  have h2 : 0 ≤ n + 3 := by addarith [hn]
  have hmul : 0 ≤ (n - 10) * (n + 3) := by positivity
  have hpoly : 0 ≤ n ^ 2 - 7 * n - 4 := by
    calc
      0 ≤ (n - 10) * (n + 3) := hmul
      _ ≤ (n - 10) * (n + 3) + 26 := by
        have h26 : (0 : ℤ) ≤ 26 := by numbers
        addarith [h26]
      _ = n ^ 2 - 7 * n - 4 := by ring
  have hn' : 0 ≤ n := by addarith [hn]
  have hmain : 0 ≤ n * (n ^ 2 - 7 * n - 4) := by positivity
  calc
    n ^ 3 - 7 * n ^ 2 = n * (n ^ 2 - 7 * n) := by ring
    _ = n * (n ^ 2 - 7 * n - 4) + 4 * n := by ring
    _ ≥ 0 + 4 * n := by rel [hmain]
    _ = 4 * n := by ring

example : {m : ℤ | m ≥ 10} ⊈ {n : ℤ | n ^ 3 - 7 * n ^ 2 ≥ 4 * n} := by
  sorry


namespace Int
example : {n : ℤ | Even n} = {a : ℤ | a ≡ 6 [ZMOD 2]} := by -- complete this
  ext x
  dsimp
  constructor
  · intro hx
    obtain ⟨k, hk⟩ := hx
    dsimp [Int.ModEq]
    use k - 3
    calc
      x - 6 = 2 * k - 6 := by rw [hk]
      _ = 2 * (k - 3) := by ring
  · intro hx
    dsimp [Int.ModEq] at hx
    obtain ⟨k, hk⟩ := hx
    use k + 3
    calc
      x = (x - 6) + 6 := by ring
      _ = 2 * k + 6 := by rw [hk]
      _ = 2 * (k + 3) := by ring

example : {n : ℤ | Even n} ≠ {a : ℤ | a ≡ 6 [ZMOD 2]} := by
  sorry
end Int


example : {t : ℝ | t ^ 2 - 5 * t + 4 = 0} = {1, 4} := by -- complete this
  ext t
  dsimp
  constructor
  · intro h
    have ht : (t - 1) * (t - 4) = 0 := by
      calc
        (t - 1) * (t - 4) = t ^ 2 - 5 * t + 4 := by ring
        _ = 0 := by rw [h]
    rw [mul_eq_zero] at ht
    obtain ht | ht := ht
    · left
      addarith [ht]
    · right
      addarith [ht]
  · intro h
    obtain h | h := h
    · calc
        t ^ 2 - 5 * t + 4 = 1 ^ 2 - 5 * 1 + 4 := by rw [h]
        _ = 0 := by numbers
    · calc
        t ^ 2 - 5 * t + 4 = 4 ^ 2 - 5 * 4 + 4 := by rw [h]
        _ = 0 := by numbers

example : {t : ℝ | t ^ 2 - 5 * t + 4 = 0} ≠ {4} := by
  sorry

example : {k : ℤ | 8 ∣ 6 * k} = {l : ℤ | 4 ∣ l} := by -- complete this
  ext n
  dsimp
  constructor
  · intro hn
    obtain ⟨a, ha⟩ := hn
    have h' : 3 * n = 4 * a := by
      have h'' : 2 * (3 * n) = 2 * (4 * a) := by
        calc
          2 * (3 * n) = 6 * n := by ring
          _ = 8 * a := by rw [ha]
          _ = 2 * (4 * a) := by ring
      cancel 2 at h''
    use n - a
    calc
      n = 4 * n - 3 * n := by ring
      _ = 4 * n - 4 * a := by rw [h']
      _ = 4 * (n - a) := by ring
  · intro hn
    obtain ⟨a, ha⟩ := hn
    use 3 * a
    calc
      6 * n = 6 * (4 * a) := by rw [ha]
      _ = 8 * (3 * a) := by ring

example : {k : ℤ | 8 ∣ 6 * k} ≠ {l : ℤ | 8 ∣ l} := by
  sorry

example : {k : ℤ | 7 ∣ 9 * k} = {l : ℤ | 7 ∣ l} := by -- complete this
  ext n
  dsimp
  constructor
  · intro hn
    obtain ⟨a, ha⟩ := hn
    use 4 * a - 5 * n
    calc
      n = 4 * (9 * n) - 5 * (7 * n) := by ring
      _ = 4 * (7 * a) - 5 * (7 * n) := by rw [ha]
      _ = 7 * (4 * a - 5 * n) := by ring
  · intro hn
    obtain ⟨a, ha⟩ := hn
    use 9 * a
    calc
      9 * n = 9 * (7 * a) := by rw [ha]
      _ = 7 * (9 * a) := by ring

example : {k : ℤ | 7 ∣ 9 * k} ≠ {l : ℤ | 7 ∣ l} := by
  sorry


example : {1, 2, 3} ≠ {1, 2} := by -- complete this
  intro h
  have h3 : (3 : ℕ) ∈ ({1, 2, 3} : Set ℕ) := by
    dsimp
    right
    right
    rfl
  have : (3 : ℕ) ∈ ({1, 2} : Set ℕ) := by rw [← h]; exact h3
  dsimp at this
  obtain h1 | h2 := this
  · numbers at h1
  · numbers at h2

example : {1, 2, 3} ≠ {1, 2} := by
  sorry

example : {x : ℝ | x ^ 2 + 3 * x + 2 = 0} = {-1, -2} := by -- complete this
  ext x
  dsimp
  constructor
  · intro h
    have hx : (x + 1) * (x + 2) = 0 := by
      calc
        (x + 1) * (x + 2) = x ^ 2 + 3 * x + 2 := by ring
        _ = 0 := by rw [h]
    rw [mul_eq_zero] at hx
    obtain hx | hx := hx
    · left
      addarith [hx]
    · right
      addarith [hx]
  · intro h
    obtain h | h := h
    · calc
        x ^ 2 + 3 * x + 2 = (-1) ^ 2 + 3 * (-1) + 2 := by rw [h]
        _ = 0 := by numbers
    · calc
        x ^ 2 + 3 * x + 2 = (-2) ^ 2 + 3 * (-2) + 2 := by rw [h]
        _ = 0 := by numbers
