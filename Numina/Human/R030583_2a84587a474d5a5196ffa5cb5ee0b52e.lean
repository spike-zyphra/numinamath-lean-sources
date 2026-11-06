import Mathlib

/-
Show that if $ a $ is an integer, then 3 divides $ a^{3} - a $.
-/
theorem number_theory_4935
    (a : ℤ) : 3 ∣ a^3 - a := by

  have h_mod : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by
    have h_nonneg : 0 ≤ a % 3 := Int.emod_nonneg a (by norm_num)
    have h_lt : a % 3 < 3 := Int.emod_lt a (by norm_num)
    interval_cases (a % 3)
    all_goals norm_num

  rcases h_mod with h0 | h1 | h2

  -- case 1 : a % 3 = 0
  . have : a ≡ 0 [ZMOD 3] := h0
    have : a ^ 3 ≡ 0 ^ 3 [ZMOD 3] := Int.ModEq.pow 3 h0
    have : a ^ 3 - a ≡ 0 ^ 3 - 0 [ZMOD 3] := Int.ModEq.sub this h0
    exact Int.dvd_of_emod_eq_zero this

  -- case 2 : a % 3 = 1
  . have : a ≡ 1 [ZMOD 3] := h1
    have : a ^ 3 ≡ 1 ^ 3 [ZMOD 3] := Int.ModEq.pow 3 h1
    have : a ^ 3 - a ≡ 1 ^ 3 - 1 [ZMOD 3] := Int.ModEq.sub this h1
    exact Int.dvd_of_emod_eq_zero this

  -- case 3 : a % 3 = 2
  . have : a ≡ 2 [ZMOD 3] := h2
    have : a ^ 3 ≡ 2 ^ 3 [ZMOD 3] := Int.ModEq.pow 3 h2
    have : a ^ 3 - a ≡ 2 ^ 3 - 2 [ZMOD 3] := Int.ModEq.sub this h2
    exact Int.dvd_of_emod_eq_zero this
