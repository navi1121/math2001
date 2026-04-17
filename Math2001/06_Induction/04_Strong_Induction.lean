/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Tactic.GCongr
import Library.Basic

math2001_init

open Nat


def F : ℕ → ℤ
  | 0 => 1
  | 1 => 1
  | n + 2 => F (n + 1) + F n

theorem F_bound (n : ℕ) : F n ≤ 2 ^ n := by
  match n with
  | 0 =>
      calc F 0 = 1 := by rw [F]
        _ ≤ 2 ^ 0 := by numbers
  | 1 =>
      calc F 1 = 1 := by rw [F]
        _ ≤ 2 ^ 1 := by numbers
  | k + 2  =>
      have IH1 := F_bound k -- first inductive hypothesis
      have IH2 := F_bound (k + 1) -- second inductive hypothesis
      calc F (k + 2) = F (k + 1) + F k := by rw [F]
        _ ≤ 2 ^ (k + 1) + 2 ^ k := by rel [IH1, IH2]
        _ ≤ 2 ^ (k + 1) + 2 ^ k + 2 ^ k := by extra
        _ = 2 ^ (k + 2) := by ring


namespace Nat

theorem exists_prime_factor {n : ℕ} (hn2 : 2 ≤ n) : ∃ p : ℕ, Prime p ∧ p ∣ n := by
  by_cases hn : Prime n
  . -- case 1: `n` is prime
    use n
    constructor
    · apply hn
    · use 1
      ring
  . -- case 2: `n` is not prime
    obtain ⟨m, hmn, _, ⟨x, hx⟩⟩ := exists_factor_of_not_prime hn hn2
    have IH : ∃ p, Prime p ∧ p ∣ m := exists_prime_factor hmn -- inductive hypothesis
    obtain ⟨p, hp, y, hy⟩ := IH
    use p
    constructor
    · apply hp
    · use x * y
      calc n = m * x := hx
        _ = (p * y) * x := by rw [hy]
        _ = p * (x * y) := by ring

/-! # Exercises -/


theorem extract_pow_two (n : ℕ) (hn : 0 < n) : ∃ a x, Odd x ∧ n = 2 ^ a * x := by --- complete this problem
  induction' n using Nat.strong_induction_on with n IH
  by_cases h_even : Even n
  · -- case: n is even
    obtain ⟨k, hk⟩ := h_even   -- n = 2k
    have hkpos : 0 < k := by
      have : n = 2 * k := by simpa [two_mul] using hk
      have : 0 < 2 * k := by simpa [this] using hn
      have : 0 < k := by extra
      exact this
    obtain ⟨a, x, hxodd, hx⟩ := IH k hkpos
    use a + 1, x
    constructor
    · exact hxodd
    · calc
        n = 2 * k := by simpa [two_mul] using hk
        _ = 2 * (2 ^ a * x) := by rw [hx]
        _ = 2 ^ (a + 1) * x := by ring
  · -- case: n is odd
      use 0, n
      constructor
      · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by
            intro h0; rw [h0] at h_even; contradiction)
        use k
        rw [hk]
        ring
      · ring
