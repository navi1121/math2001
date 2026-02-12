/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

/-! # Section 1.4: Proving inequalities -/


-- Example 1.4.1
example {x y : ℤ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 :=
  calc
    y = y + 2 * x - 2 * x := by ring
    _ ≥ 3 - 2 * x := by rel [hy]
    _ = 9 - 2 * (x + 3) := by ring
    _ ≥ 9 - 2 * 2 := by rel [hx]
    _ > 3 := by numbers

-- Example 1.4.2
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {r s : ℚ} (h1 : s + 3 ≥ r) (h2 : s + r ≤ 3) : r ≤ 3 :=
  calc
    r = (s + r + r - s) / 2 := by ring
    _ ≤ (3 + (s + 3) - s) / 2 := by rel [h1, h2]
    _ = 3 := by ring

-- Example 1.4.3
-- Exercise: type out the whole proof printed in the text as a Lean proof.
example {x y : ℝ} (h1 : y ≤ x + 5) (h2 : x ≤ -2) : x + y < 2 :=
  calc
    x + y ≤ x + (x + 5) := by rel [h1]
    _ = 2 * x + 5 := by ring
    _ ≤ 2 * (-2) + 5 := by rel [h2]
    _ < 2 := by numbers

-- Example 1.4.4
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {u v x y A B : ℝ} (h1 : 0 < A) (h2 : A ≤ 1) (h3 : 1 ≤ B) (h4 : x ≤ B)
    (h5 : y ≤ B) (h6 : 0 ≤ u) (h7 : 0 ≤ v) (h8 : u < A) (h9 : v < A) :
    u * y + v * x + u * v < 3 * A * B :=
  calc
    u * y + v * x + u * v
      ≤ u * B + v * B + u * v := by rel [h1, h2, h4, h5]
    _ ≤ A * B + A * B + A * v := by rel [h1, h2, h3, h6, h7, h8, h9]
    _ ≤ A * B + A * B + 1 * v := by rel [h1, h2, h3, h6, h7, h8, h9]
    _ ≤ A * B + A * B + B * v := by rel [h1, h2, h3, h6, h7, h8, h9]
    _ < A * B + A * B + B * A := by rel [h1, h2, h3, h6, h7, h8, h9]
    _ = 3 * A * B := by ring

-- Example 1.4.5
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {t : ℚ} (ht : t ≥ 10) : t ^ 2 - 3 * t - 17 ≥ 5 :=
  calc
    t ^ 2 - 3 * t - 17
      = t * t - 3 * t - 17 := by ring
    _ ≥ 10 * t - 3 * t - 17 := by rel [ht]
    _ = 7 * t - 17 := by ring
    _ ≥ 7 * 10 - 17 := by rel [ht]
    _ ≥ 5 := by numbers

-- Example 1.4.6
-- Exercise: type out the whole proof printed in the text as a Lean proof.
example {n : ℤ} (hn : n ≥ 5) : n ^ 2 > 2 * n + 11 :=
  calc
    n ^ 2 = n * n := by ring
    _ ≥ 5 * n := by rel [hn]
    _ = 2 * n + 3 * n := by ring
    _ ≥ 2 * n + 3 * 5 := by rel [hn]
    _ = 2 * n + 11 + 4 := by ring
    _ > 2 * n + 11 := by extra

-- Example 1.4.7
example {m n : ℤ} (h : m ^ 2 + n ≤ 2) : n ≤ 2 :=
  calc
    n ≤ m ^ 2 + n := by extra
    _ ≤ 2 := by rel [h]


-- Example 1.4.8
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {x y : ℝ} (h : x ^ 2 + y ^ 2 ≤ 1) : (x + y) ^ 2 < 3 :=
  calc
    (x + y) ^ 2 ≤ (x + y) ^ 2 + (x - y) ^ 2 := by extra
    _ = 2 * (x ^ 2 + y ^ 2) := by ring
    _ ≤ 2 * 1 := by rel [h]
    _ < 3 := by numbers

-- Example 1.4.9
-- Exercise: replace the words "sorry" with the correct Lean justification.
example {a b : ℚ} (h1 : a ≥ 0) (h2 : b ≥ 0) (h3 : a + b ≤ 8) :
    3 * a * b + a ≤ 7 * b + 72 :=
  calc
    3 * a * b + a
      ≤ 2 * b ^ 2 + a ^ 2 + (3 * a * b + a) := by extra
    _ = 2 * ((a + b) * b) + (a + b) * a + a := by ring
    _ ≤ 2 * (8 * b) + 8 * a + a := by rel [h1, h2, h3]
    _ = 7 * b + 9 * (a + b) := by ring
    _ ≤ 7 * b + 9 * 8 := by rel[h3]
    _ = 7 * b + 72 := by ring

-- Example 1.4.10
example {a b c : ℝ} :
    a ^ 2 * (a ^ 6 + 8 * b ^ 3 * c ^ 3) ≤ (a ^ 4 + b ^ 4 + c ^ 4) ^ 2 :=
  calc
    a ^ 2 * (a ^ 6 + 8 * b ^ 3 * c ^ 3)
      ≤ 2 * (a ^ 2 * (b ^ 2 - c ^ 2)) ^ 2 + (b ^ 4 - c ^ 4) ^ 2
          + 4 * (a ^ 2 * b * c - b ^ 2 * c ^ 2) ^ 2
          + a ^ 2 * (a ^ 6 + 8 * b ^ 3 * c ^ 3) := by extra
    _ = (a ^ 4 + b ^ 4 + c ^ 4) ^ 2 := by ring


/-! # Exercises

Solve these problems yourself.  You may find it helpful to solve them on paper before typing them
up in Lean. -/


example {x y : ℤ} (h1 : x + 3 ≥ 2 * y) (h2 : 1 ≤ y) : x ≥ -1 :=
  calc
    x = x + 3 - 3 := by ring
    _ ≥ 2 * y - 3 := by rel [h1]
    _ ≥ 2 * 1 - 3 := by rel [h2]
    _ = -1 := by ring

example {a b : ℚ} (h1 : 3 ≤ a) (h2 : a + 2 * b ≥ 4) : a + b ≥ 3 :=
  have h3 : b ≥ 2 - a / 2 := by
    have : 2 * b ≥ 4 - a := by
      calc 2 * b = a + 2 * b - a := by ring
        _ ≥ 4 - a := by rel [h2]
    calc b = 2 * b / 2 := by ring
      _ ≥ (4 - a) / 2 := by rel [this]
      _ = 2 - a / 2 := by ring
  calc
    a + b ≥ a + (2 - a / 2) := by rel [h3]
    _ = a + 2 - a / 2 := by ring
    _ = a / 2 + 2 := by ring
    _ ≥ 3 / 2 + 2 := by rel [h1]
    _ = 7 / 2 := by ring
    _ ≥ 3 := by numbers

example {x : ℤ} (hx : x ≥ 9) : x ^ 3 - 8 * x ^ 2 + 2 * x ≥ 3 :=
  have h1 : x - 8 ≥ 0 := by
    calc x - 8 ≥ 9 - 8 := by rel [hx]
      _ = 1 := by ring
      _ ≥ 0 := by numbers
  calc
    x ^ 3 - 8 * x ^ 2 + 2 * x
        = x ^ 2 * (x - 8) + 2 * x := by ring
    _ ≥ 9 ^ 2 * (x - 8) + 2 * x := by rel [hx, h1]
    _ = 81 * (x - 8) + 2 * x := by ring
    _ ≥ 81 * (9 - 8) + 2 * 9 := by rel [hx]
    _ = 81 + 18 := by ring
    _ = 99 := by ring
    _ ≥ 3 := by numbers

example {n : ℤ} (hn : n ≥ 10) : n ^ 4 - 2 * n ^ 2 > 3 * n ^ 3 :=
  have h1 : n ^ 2 ≥ 100 := by
    calc n ^ 2 ≥ 10 ^ 2 := by rel [hn]
      _ = 100 := by ring
  have h2 : n ^ 2 - 3 * n - 2 ≥ 68 := by
    have hpos1 : 0 ≤ n - 10 := by
      calc n - 10 ≥ 10 - 10 := by rel [hn]
        _ = 0 := by ring
    have hpos2 : 0 ≤ n + 7 := by
      calc n + 7 ≥ 10 + 7 := by rel [hn]
        _ = 17 := by ring
        _ ≥ 0 := by numbers
    have hmul : 0 ≤ (n - 10) * (n + 7) := by apply mul_nonneg <;> assumption
    calc n ^ 2 - 3 * n - 2 = (n - 10) * (n + 7) + 68 := by ring
      _ ≥ 0 + 68 := by rel [hmul]
      _ = 68 := by ring
  have h3 : n ^ 2 - 3 * n - 2 ≥ 0 := by
    calc n ^ 2 - 3 * n - 2 ≥ 68 := h2
      _ ≥ 0 := by numbers
  have h4 : n ^ 2 * (n ^ 2 - 3 * n - 2) ≥ 6800 := by
    calc n ^ 2 * (n ^ 2 - 3 * n - 2)
        ≥ 100 * (n ^ 2 - 3 * n - 2) := by rel [h1, h3]
      _ ≥ 100 * 68 := by rel [h2]
      _ = 6800 := by ring
  have h5 : n ^ 4 - 2 * n ^ 2 - 3 * n ^ 3 > 0 :=
    calc
      n ^ 4 - 2 * n ^ 2 - 3 * n ^ 3
          = n ^ 2 * (n ^ 2 - 3 * n - 2) := by ring
      _ ≥ 6800 := h4
      _ > 0 := by numbers
  calc n ^ 4 - 2 * n ^ 2 = (n ^ 4 - 2 * n ^ 2 - 3 * n ^ 3) + 3 * n ^ 3 := by ring
    _ > 0 + 3 * n ^ 3 := by exact (add_lt_add_right h5 (3 * n ^ 3))
    _ = 3 * n ^ 3 := by ring

example {n : ℤ} (h1 : n ≥ 5) : n ^ 2 - 2 * n + 3 > 14 :=
  calc
    n ^ 2 - 2 * n + 3 = (n - 1) ^ 2 + 2 := by ring
    _ ≥ (5 - 1) ^ 2 + 2 := by rel [h1]
    _ = 4 ^ 2 + 2 := by ring
    _ = 16 + 2 := by ring
    _ = 18 := by numbers
    _ > 14 := by numbers

example {x : ℚ} : x ^ 2 - 2 * x ≥ -1 :=
  calc
    x ^ 2 - 2 * x = (x - 1) ^ 2 - 1 := by ring
    _ ≥ 0 - 1 := by extra
    _ = -1 := by ring

example (a b : ℝ) : a ^ 2 + b ^ 2 ≥ 2 * a * b :=
  calc
    a ^ 2 + b ^ 2 = (a - b) ^ 2 + 2 * a * b := by ring
    _ ≥ 0 + 2 * a * b := by
      apply add_le_add_right
      exact sq_nonneg (a - b)
    _ = 2 * a * b := by ring
