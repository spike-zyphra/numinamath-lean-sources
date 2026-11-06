import Mathlib

lemma pow_two_mod_zero_of_even {a : ℤ} (ha : Even a) : a^2 % 4 = 0 := by
  -- First, it is easy to get that $a^2 \% 4 = 0$ given that $a$ is even.
  rcases ha with ⟨n, han⟩
  rw [han,(show (n + n)^2 = n^2 * 4 by ring)]
  simp_all

lemma number_theory_4669_aux : ∀ (a b : ℤ), (a^2 + b^2) % 4 ≠ 3 := by
  -- Then, we show that $a^2 + b^2 \neq 3$
  intro a b
  cases Int.even_or_odd a with
  | inl ha =>
    cases Int.even_or_odd b with
    | inl hb =>
      -- If $a$ and $b$ are both even, then $a^2 \% 4 = 0$ and $b^2 \% 4 = 0$.
      have h1 : a^2 % 4 = 0 := pow_two_mod_zero_of_even ha
      have h2 : b^2 % 4 = 0 := pow_two_mod_zero_of_even hb
      -- Thus, $(a^2 + b^2) \% 4 = 0$.
      have : (a^2 + b^2) % 4 = 0 := by
        rw [Int.add_emod,h1,h2]
        rfl
      -- So, $a^2 + b^2 \neq 3$.
      linarith
    | inr hb =>
      -- If $a$ is even and $b$ is odd, then $a^2 \% 4 = 0$ and $b^2 \% 4 = 1$.
      have h1 : a^2 % 4 = 0 := pow_two_mod_zero_of_even ha
      have h2 : b^2 % 4 = 1 := Int.sq_mod_four_eq_one_of_odd hb
      -- Thus, $(a^2 + b^2) \% 4 = 1$.
      have : (a^2 + b^2) % 4 = 1 := by
        rw [Int.add_emod,h1,h2]
        rfl
      -- So, $a^2 + b^2 \neq 3$.
      linarith
  | inr ha =>
    cases Int.even_or_odd b with
    | inl hb =>
      -- If $a$ is odd and $b$ is even, then $a^2 \% 4 = 1$ and $b^2 \% 4 = 0$.
      have h1 : a^2 % 4 = 1 := Int.sq_mod_four_eq_one_of_odd ha
      have h2 : b^2 % 4 = 0 := pow_two_mod_zero_of_even hb
      -- Thus, $(a^2 + b^2) \% 4 = 1$.
      have : (a^2 + b^2) % 4 = 1 := by
        rw [Int.add_emod,h1,h2]
        rfl
      -- So, $a^2 + b^2 \neq 3$.
      linarith
    | inr hb =>
      -- If $a$ and $b$ are both odd, then $a^2 \% 4 = 1$ and $b^2 \% 4 = 1$.
      have h1 : a^2 % 4 = 1 := Int.sq_mod_four_eq_one_of_odd ha
      have h2 : b^2 % 4 = 1 := Int.sq_mod_four_eq_one_of_odd hb
      -- Thus, $(a^2 + b^2) \% 4 = 2$.
      have : (a^2 + b^2) % 4 = 2 := by
        rw [Int.add_emod,h1,h2]
        rfl
      -- So, $a^2 + b^2 \neq 3$.
      linarith

theorem number_theory_4669 {n : ℤ} : n ≡ 3 [ZMOD 4] → ¬∃ (a b : ℤ), n = a^2 + b^2 := by 
  intro hn
  intro h
  rcases h with ⟨a, b, hn1⟩
  have h1 : (a^2 + b^2) % 4 ≠ 3 := number_theory_4669_aux a b
  have h2 : (a^2 + b^2) % 4 = 3 := by
    have h3 : a^2 + b^2 = n := by
      linarith
    rw [h3]
    norm_num [Int.ModEq] at hn ⊢
    omega
  contradiction
  all_goals tauto