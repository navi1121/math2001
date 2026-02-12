/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Tactic.GCongr
import Library.Basic
import AutograderLib

math2001_init

/-! # Homework 0

Don't forget to compare with the text version
for clearer statements and any special instructions. -/


@[autograded 5]
theorem problem1 {n : ℤ} (hn : n ≥ 5) : n ^ 2 > 2 * n + 11 :=
  by
  -- write n = 5 + k with k ≥ 0 and expand
  let k := n - 5
  have hk : 0 ≤ k := by rel [hn]
  have : n = 5 + k := by ring
  calc
    n ^ 2 - 2 * n - 11
        = (5 + k) ^ 2 - 2 * (5 + k) - 11 := by rw [this]; ring
    _ = 4 + k * (8 + k) := by ring
    _ ≥ 4 + 0 := by
      apply add_le_add_left
      apply mul_nonneg
      · exact hk
      · calc
          8 + k ≥ 8 := by apply add_le_add_right; exact hk
          _ ≥ 0 := by numbers
    _ > 0 := by numbers
