/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Theory.ModEq.Defs

math2001_init

namespace Int


example : ∃! a : ℝ, 3 * a + 1 = 7 := by
  use 2
  dsimp
  constructor
  · numbers
  intro y hy
  calc
    y = (3 * y + 1 - 1) / 3 := by ring
    _ = (7 - 1) / 3 := by rw [hy]
    _ = 2 := by numbers


example : ∃! x : ℚ, ∀ a, a ≥ 1 → a ≤ 3 → (a - x) ^ 2 ≤ 1 := by
  sorry

example {x : ℚ} (hx : ∃! a : ℚ, a ^ 2 = x) : x = 0 := by
  obtain ⟨a, ha1, ha2⟩ := hx
  have h1 : -a = a
  · apply ha2
    calc
      (-a) ^ 2 = a ^ 2 := by ring
      _ = x := ha1
  have h2 :=
    calc
      a = (a - -a) / 2 := by ring
      _ = (a - a) / 2 := by rw [h1]
      _ = 0 := by ring
  calc
    x = a ^ 2 := by rw [ha1]
    _ = 0 ^ 2 := by rw [h2]
    _ = 0 := by ring


example : ∃! r : ℤ, 0 ≤ r ∧ r < 5 ∧ 14 ≡ r [ZMOD 5] := by
  use 4
  dsimp
  constructor
  · constructor
    · numbers
    constructor
    · numbers
    use 2
    numbers
  intro r hr
  obtain ⟨hr1, hr2, q, hr3⟩ := hr
  have :=
    calc
      5 * 1 < 14 - r := by addarith [hr2]
      _ = 5 * q := by rw [hr3]
  cancel 5 at this
  have :=
    calc
      5 * q = 14 - r := by rw [hr3]
      _ < 5 * 3 := by addarith [hr1]
  cancel 5 at this
  interval_cases q
  addarith [hr3]

/-! # Exercises -/


example : ∃! x : ℚ, 4 * x - 3 = 9 := by ------
  use 3
  dsimp
  constructor
  · numbers
  · intro y hy
    have : y = (4 * y - 3 + 3) / 4 := by ring
    calc y = (4 * y - 3 + 3) / 4 := by ring
      _ = (9 + 3) / 4             := by rw [hy]
      _ = 3                       := by numbers

example : ∃! n : ℕ, ∀ a, n ≤ a := by
  sorry

example : ∃! r : ℤ, 0 ≤ r ∧ r < 3 ∧ 11 ≡ r [ZMOD 3] := by ------
  use 2
  dsimp
  constructor
  · -- Show 2 satisfies all three conditions
    constructor
    · numbers                    -- 0 ≤ 2
    constructor
    · numbers                    -- 2 < 3
    · use 3; numbers             -- 11 ≡ 2 [ZMOD 3]:  11 - 2 = 3 * 3
  · -- Uniqueness: any r satisfying the conditions equals 2
    intro r hr
    obtain ⟨hr0, hr3, hr11⟩ := hr
    obtain ⟨q, hq⟩ := hr11      -- hq : 11 - r = 3 * q
    -- Bound q from below: r < 3 → 11 - r > 8 → 3q > 8 → q ≥ 3
    have hqlo : 2 < q := by
      have h1 : 11 - r > 8 := by addarith [hr3]
      have h2 : 3 * q > 8  := by addarith [hq, h1]
      have h3 : 3 * 2 < 3 * q := by addarith [h2]
      cancel 3 at h3
    -- Bound q from above: r ≥ 0 → 11 - r ≤ 11 → 3q ≤ 11 → q ≤ 3
    have hqhi : q < 4 := by
      have h1 : 11 - r ≤ 11    := by addarith [hr0]
      have h2 : 3 * q ≤ 11     := by addarith [hq, h1]
      have h3 : 3 * q < 3 * 4  := by addarith [h2]
      cancel 3 at h3
    -- q must be 3 (only integer with 2 < q < 4)
    interval_cases q
    -- Only one case: q = 3
    addarith [hq]                -- 11 - r = 9 → r = 2
