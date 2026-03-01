/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init


example {a : ℚ} (h : ∃ b : ℚ, a = b ^ 2 + 1) : a > 0 := by
  obtain ⟨b, hb⟩ := h
  calc
    a = b ^ 2 + 1 := hb
    _ > 0 := by extra


example {t : ℝ} (h : ∃ a : ℝ, a * t < 0) : t ≠ 0 := by
  obtain ⟨x, hxt⟩ := h
  have H := le_or_gt x 0
  obtain hx | hx := H
  · have hxt' : 0 < (-x) * t := by addarith [hxt]
    have hx' : 0 ≤ -x := by addarith [hx]
    cancel -x at hxt'
    apply ne_of_gt
    apply hxt'
  · have hxt' : 0 < x * (-t) := by
      calc x * (-t) = -(x * t) := by ring
        _ > 0 := by addarith [hxt]
    have hx' : 0 ≤ x := by addarith [hx]
    cancel x at hxt'
    apply ne_of_lt
    addarith [hxt']

example : ∃ n : ℤ, 12 * n = 84 := by
  use 7
  numbers


example (x : ℝ) : ∃ y : ℝ, y > x := by
  use x + 1
  extra


example : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 11 := by
  use 6, 5
  numbers

example (a : ℤ) : ∃ m n : ℤ, m ^ 2 - n ^ 2 = 2 * a + 1 := by
  use a + 1, a
  ring

example {p q : ℝ} (h : p < q) : ∃ x, p < x ∧ x < q := by
  use (p + q ) /2
  constructor
  · calc p = (p + p) / 2 := by ring
    _ < (p + q) / 2 := by rel [h]
  · calc q = (q + q) /2 := by ring
    _ > (p + q) / 2 := by rel [h]


example : ∃ a b c d : ℕ,
    a ^ 3 + b ^ 3 = 1729 ∧ c ^ 3 + d ^ 3 = 1729 ∧ a ≠ c ∧ a ≠ d := by
  use 1, 12, 9, 10
  constructor
  numbers
  constructor
  numbers
  constructor
  numbers
  numbers

/-! # Exercises -/


example : ∃ t : ℚ, t ^ 2 = 1.69 := by
  use 1.3
  numbers

example : ∃ m n : ℤ, m ^ 2 + n ^ 2 = 85 := by
  use 9, 2
  numbers

example : ∃ x : ℝ, x < 0 ∧ x ^ 2 < 1 := by
  use -1/2
  constructor
  · numbers
  · numbers

example : ∃ a b : ℕ, 2 ^ a = 5 * b + 1 := by
  use 4,3
  numbers

example (x : ℚ) : ∃ y : ℚ, y ^ 2 > x := by
  use x + 1
  have h : (x + 1) ^ 2 = x + (x ^ 2 + x + 1) := by ring
  have h2 : x ^ 2 + x + 1 > 0 := by
    have : (x + 1 / 2) ^ 2 + 3 / 4 > 0 := by extra
    calc x ^ 2 + x + 1 = (x + 1 / 2) ^ 2 + 3 / 4 := by ring
      _ > 0 := by extra
  calc (x + 1) ^ 2 = x + (x ^ 2 + x + 1) := by ring
    _ > x + 0 := by rel [h2]
    _ = x := by ring

example {t : ℝ} (h : ∃ a : ℝ, a * t + 1 < a + t) : t ≠ 1 := by
  obtain ⟨a, ha⟩ := h
  have H := le_or_gt a 1
  obtain ha1 | ha1 := H
  · have h1 : (1 - a) * (t - 1) > 0 := by
      calc (1 - a) * (t - 1) = -(a * t + 1 - (a + t)) := by ring
        _ > 0 := by addarith [ha]
    have h2 : 0 ≤ 1 - a := by addarith [ha1]
    cancel (1 - a) at h1
    apply ne_of_gt
    addarith [h1]
  · have h1 : (a - 1) * (1 - t) > 0 := by
      calc (a - 1) * (1 - t) = -(a * t + 1 - (a + t)) := by ring
        _ > 0 := by addarith [ha]
    have h2 : 0 < a - 1 := by addarith [ha1]
    cancel (a - 1) at h1
    apply ne_of_lt
    addarith [h1]

example {m : ℤ} (h : ∃ a, 2 * a = m) : m ≠ 5 := by
  obtain ⟨a, ha⟩ := h
  have H := le_or_succ_le a 2
  obtain ha2 | ha2 := H
  · apply ne_of_lt
    calc m = 2 * a := by addarith [ha]
      _ ≤ 2 * 2 := by rel [ha2]
      _ < 5 := by numbers
  · apply ne_of_gt
    calc m = 2 * a := by addarith [ha]
      _ ≥ 2 * 3 := by rel [ha2]
      _ > 5 := by numbers

example {n : ℤ} : ∃ a, 2 * a ^ 3 ≥ n * a + 7 := by
  use n ^ 2 + 4
  have h : 2 * (n ^ 2 + 4) ^ 3 - n * (n ^ 2 + 4) - 7 =
           2 * n ^ 6 + 24 * n ^ 4 + 96 * n ^ 2 + 128
           - n ^ 3 - 4 * n - 7 := by ring
  have h2 : 2 * n ^ 6 + 24 * n ^ 4 - n ^ 3 + 96 * n ^ 2 - 4 * n + 121 ≥ 0 := by extra
  addarith [h, h2]

example {a b c : ℝ} (ha : a ≤ b + c) (hb : b ≤ a + c) (hc : c ≤ a + b) :
    ∃ x y z, x ≥ 0 ∧ y ≥ 0 ∧ z ≥ 0 ∧ a = y + z ∧ b = x + z ∧ c = x + y := by
  use (b + c - a) / 2, (a + c - b) / 2, (a + b - c) / 2
  refine ⟨by addarith [ha], by addarith [hb], by addarith [hc], by ring, by ring, by ring⟩
