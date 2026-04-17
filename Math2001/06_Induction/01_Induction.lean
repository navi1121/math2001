/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic
import Library.Tactic.ModEq

math2001_init

namespace Nat


example (n : ℕ) : 2 ^ n ≥ n + 1 := by
  simple_induction n with k IH
  · -- base case
    numbers
  · -- inductive step
    calc 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      _ ≥ 2 * (k + 1) := by rel [IH]
      _ = (k + 1 + 1) + k := by ring
      _ ≥ k + 1 + 1 := by extra


example (n : ℕ) : Even n ∨ Odd n := by
  simple_induction n with k IH
  · -- base case
    sorry
  · -- inductive step
    obtain ⟨x, hx⟩ | ⟨x, hx⟩ := IH
    · sorry
    · sorry

example {a b d : ℤ} (h : a ≡ b [ZMOD d]) (n : ℕ) : a ^ n ≡ b ^ n [ZMOD d] := by
  sorry

example (n : ℕ) : 4 ^ n ≡ 1 [ZMOD 15] ∨ 4 ^ n ≡ 4 [ZMOD 15] := by
  simple_induction n with k IH
  · -- base case
    left
    numbers
  · -- inductive step
    obtain hk | hk := IH
    · right
      calc (4:ℤ) ^ (k + 1) = 4 * 4 ^ k := by ring
        _ ≡ 4 * 1 [ZMOD 15] := by rel [hk]
        _ = 4 := by numbers
    · left
      calc (4:ℤ) ^ (k + 1) = 4 * 4 ^ k := by ring
        _ ≡ 4 * 4 [ZMOD 15] := by rel [hk]
        _ = 15 * 1 + 1 := by numbers
        _ ≡ 1 [ZMOD 15] := by extra


example {n : ℕ} (hn : 2 ≤ n) : (3:ℤ) ^ n ≥ 2 ^ n + 5 := by
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    numbers
  · -- inductive step
    calc (3:ℤ) ^ (k + 1) = 2 * 3 ^ k + 3 ^ k := by ring
      _ ≥ 2 * (2 ^ k + 5) + 3 ^ k := by rel [IH]
      _ = 2 ^ (k + 1) + 5 + (5 + 3 ^ k) := by ring
      _ ≥ 2 ^ (k + 1) + 5 := by extra


example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 := by
  dsimp
  use 4
  intro n hn
  induction_from_starting_point n, hn with k hk IH
  · -- base case
    sorry
  · -- inductive step
    sorry


/-! # Exercises -/


example (n : ℕ) : 3 ^ n ≥ n ^ 2 + n + 1 := by --- complete this problem
  simple_induction n with k IH
  · --base case
    numbers
  · --inductive step
    calc
      3 ^ (k + 1) = 3 * 3 ^ k := by ring
      _ = 3 * k^2 + 3 * k + 3 := by ring
      _ ≥ k^2 + 3*k + 3 := by extra
      _ = (k+1)^2 + (k+1) + 1 := by ring


example {a : ℝ} (ha : -1 ≤ a) (n : ℕ) : (1 + a) ^ n ≥ 1 + n * a := by
  sorry

example (n : ℕ) : 5 ^ n ≡ 1 [ZMOD 8] ∨ 5 ^ n ≡ 5 [ZMOD 8] := by --- complete this problem
    simple_induction n with k IH
    · left
      numbers
    · obtain h | h := IH
      · right
        calc
          5 ^ (k + 1)
              = 5 * 5 ^ k := by ring
          _ ≡ 5 * 1 [ZMOD 8] := by rel [h]
          _ ≡ 5 [ZMOD 8] := by numbers
      · left
        calc
          5 ^ (k + 1)
              = 5 * 5 ^ k := by ring
          _ ≡ 5 * 5 [ZMOD 8] := by rel [h]
          _ ≡ 1 [ZMOD 8] := by numbers

example (n : ℕ) : 6 ^ n ≡ 1 [ZMOD 7] ∨ 6 ^ n ≡ 6 [ZMOD 7] := by
  sorry

example (n : ℕ) :
    4 ^ n ≡ 1 [ZMOD 7] ∨ 4 ^ n ≡ 2 [ZMOD 7] ∨ 4 ^ n ≡ 4 [ZMOD 7] := by --- complete this problem
  simple_induction n with k IH
  · left
    numbers
  · obtain h1 | h2 | h3 := IH
    · right; right
      calc
        4 ^ (k + 1)
            = 4 * 4 ^ k := by ring
        _ ≡ 4 * 1 [ZMOD 7] := by rel [h1]
        _ ≡ 4 [ZMOD 7] := by numbers
    · left
      calc
        4 ^ (k + 1)
            = 4 * 4 ^ k := by ring
        _ ≡ 4 * 2 [ZMOD 7] := by rel [h2]
        _ ≡ 1 [ZMOD 7] := by numbers
    · right; left
      calc
        4 ^ (k + 1)
            = 4 * 4 ^ k := by ring
        _ ≡ 4 * 4 [ZMOD 7] := by rel [h3]
        _ ≡ 2 [ZMOD 7] := by numbers

example : forall_sufficiently_large n : ℕ, (3:ℤ) ^ n ≥ 2 ^ n + 100 := by
  dsimp
  sorry

example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 2 + 4 := by --- complete this problem
  dsimp
  use 4
  intro n hn
  simple_induction n with k IH
  · numbers
  · calc
      2 ^ (k + 1)
          = 2 * 2 ^ k := by ring
      _ ≥ 2 * (k ^ 2 + 4) := by rel [IH]
      _ = 2 * k ^ 2 + 8 := by ring
      _ ≥ (k + 1) ^ 2 + 4 := by extra

example : forall_sufficiently_large n : ℕ, 2 ^ n ≥ n ^ 3 := by
  dsimp
  sorry

theorem Odd.pow {a : ℕ} (ha : Odd a) (n : ℕ) : Odd (a ^ n) := by --- complete this problem
  simple_induction n with k IH
  · -- base case: a^0 = 1
    numbers
  · -- inductive step
    have hmul : Odd (a * a ^ k) := by
      -- odd * odd = odd
      obtain ⟨m, hm⟩ := ha
      obtain ⟨t, ht⟩ := IH
      use (2 * m * a ^ k + t)
      calc
        a * a ^ k
            = (2 * m + 1) * (2 * t + 1) := by rw [hm, ht]
        _ = 2 * (m * (2 * t + 1) + t) + 1 := by ring

    -- rewrite power
    have : a ^ (k + 1) = a * a ^ k := by ring
    rw [this]
    exact hmul

theorem Nat.even_of_pow_even {a n : ℕ} (ha : Even (a ^ n)) : Even a := by
  sorry
