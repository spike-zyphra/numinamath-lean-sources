import Mathlib

/- All natural numbers greater than one were painted in two colors - blue and red - such that
the sum of any two blue numbers (including identical ones) is blue,
and the product of any two red numbers (including identical ones) is red.
It is known that both colors were used in the painting and that the number 1024 was painted blue.
What color could the number 2017 be in this case?
-/

theorem number_theory_251087 {blue red : Set ℕ} (h1: ∀ n: ℕ, 1 < n → n ∈ blue ∨ n ∈ red)
 (h2: Disjoint blue red) (h3 : 1024 ∈ blue) (h4: ∃ k: ℕ, 1 < k ∧ k ∈ red)
 (hb : ∀ m ∈ blue, ∀ n ∈ blue, m + n ∈ blue)
  (hr : ∀ m ∈ red, ∀ n ∈ red, m * n ∈ red): 2017 ∈ red := by
  
  -- we prove by contradiction
  by_contra! h
  replace h: 2017 ∈ blue := by
    specialize h1 2017
    norm_num at h1
    simp [h] at h1
    exact h1

  -- we start by showing that if m is red, then m^n is red for all n ≥ 1
  have red_pow: ∀ m ∈ red, ∀ n: ℕ, m ^ (n + 1) ∈ red := by
    intro m hm n
    induction' n with n ih
    -- base case n = 0
    .
      norm_num
      exact hm
    -- inductive step
    .
      have eq: m ^ (n + 1 + 1) = m ^ (n + 1) * m := by
        rw [Nat.pow_add_one]
      rw [eq]
      clear eq
      specialize hr (m ^ (n + 1)) ih m hm
      exact hr

  -- then we show that 2 is blue
  have b2: 2 ∈ blue := by
    by_contra! o
    replace o: 2 ∈ red := by
      specialize h1 2
      norm_num at h1
      simp [o] at h1
      exact h1
    specialize red_pow 2 o 9
    rw [show 2 ^ (9 + 1) = 1024 by norm_num] at red_pow
    absurd h2
    rw [Set.not_disjoint_iff]
    use 1024

  -- then we deduce that any even number is blue
  have b_even: ∀ n: ℕ, 2 * n + 2 ∈ blue := by
    intro n
    induction' n with n ih
    -- base case n = 0
    .
      norm_num
      exact b2
    -- inductive step
    .
      rw [show 2 * (n + 1) + 2 = 2 * n + 2 + 2 by ring]
      specialize hb (2 * n + 2) ih 2 b2
      exact hb

  -- then we must have k is odd
  obtain ⟨k, hk⟩:= h4
  rcases hk with ⟨lk, hk⟩
  have ok: Odd k := by
    by_contra! ok
    simp at ok
    rw [even_iff_exists_two_mul] at ok
    obtain ⟨m, hm⟩:= ok
    have lm: 1 ≤ m := by omega
    set n:= m - 1 with hn
    replace hn: m = n + 1 := by
      rw [hn]
      omega
    rw [hn] at hm
    specialize b_even n
    rw [show 2 * (n + 1) = 2 * n + 2 by ring] at hm
    rw [← hm] at b_even
    absurd h2
    rw [Set.not_disjoint_iff]
    use k

  -- we choose n = 11 such that k ^ n is more that 2017, we write k ^ 11 = (k ^ 11 - 2017) + 2017
  specialize red_pow k hk 10
  rw [show 10 + 1 = 11 by norm_num] at red_pow
  have s: 2 ^ 11 ≤ k ^ 11 := by
    apply Nat.pow_le_pow_left
    omega
  norm_num at s
  set r:= k ^ 11 - 2017 with hr
  have er: Even r := by
    rw [hr]
    rw [Nat.even_sub']
    constructor
    .
      intro l
      decide
    .
      intro l
      apply Odd.pow
      exact ok
    omega
  rw [even_iff_exists_two_mul] at er
  obtain ⟨m, hm⟩:= er
  have lm: 1 ≤ m := by omega
  set n:= m - 1 with hn
  replace hn: m = n + 1 := by
    rw [hn]
    omega
  simp [hn] at hm
  rw [show 2 * (n + 1) = 2 * n + 2 by ring] at hm
  specialize b_even n
  rw [← hm] at b_even
  specialize hb r b_even 2017 h
  simp [hr] at hb
  rw [show k ^ 11 - 2017 + 2017 = k ^ 11 by omega] at hb
  absurd h2
  rw [Set.not_disjoint_iff]
  use k ^ 11
  