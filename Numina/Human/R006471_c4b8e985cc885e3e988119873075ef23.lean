import Mathlib
/- Let $K$ be a positive integer. Show that there is a natural number $n$ such that $n!$ ends in at least $K$ zeros. -/
theorem number_theory_637441 (k : ℕ) (hk : k > 0) : ∃ n : ℕ, 10 ^ k ∣ Nat.factorial n:= by
  -- Proof by induction on k
  induction k with
  -- Base case: k = 0 (though this case is not actually used due to hk : k > 0)
  | zero =>
    use 1
    simp
  -- Inductive case: prove for k + 1 assuming it's true for k
  | succ k ih =>
    -- Handle special case when k = 0
    by_cases hk1 : k = 0
    .
      subst k
      use 5
      simp [Nat.factorial_succ]
      omega
    .
      -- Use induction hypothesis for k > 0
      replace ih:= ih (by omega)
      rcases ih with ⟨n, hn⟩
      -- Choose n + 10 as our new number
      use (n + 10)
      -- Expand factorial using successive multiplications
      repeat rw [Nat.factorial_succ]
      -- Rearrange the factorial expression
      rw [show (n + 9 + 1) * ((n + 8 + 1) * ((n + 7 + 1) * ((n + 6 + 1) * ((n + 5 + 1) * ((n + 4 + 1) * ((n + 3 + 1) * ((n + 2 + 1) * ((n + 1 + 1) * ((n + 1) * n.factorial))))))))) = (n + 9 + 1) * (n + 8 + 1) * (n + 7 + 1) * (n + 6 + 1) * (n + 5 + 1) * (n + 4 + 1) * (n + 3 + 1) * (n + 2 + 1) * (n + 1 + 1) * (n + 1) * n.factorial by ring]

      -- Prove that 10 divides the product of consecutive numbers from n+1 to n+10
      have h1 : 10 ∣ (n + 9 + 1) * (n + 8 + 1) * (n + 7 + 1) * (n + 6 + 1) * (n + 5 + 1) * (n + 4 + 1) * (n + 3 + 1) * (n + 2 + 1) * (n + 1 + 1) * (n + 1):= by
        -- Simplify the expression
        rw [show (n + 9 + 1) * (n + 8 + 1) * (n + 7 + 1) * (n + 6 + 1) * (n + 5 + 1) * (n + 4 + 1) * (n + 3 + 1) * (n + 2 + 1) * (n + 1 + 1) * (n + 1) = (n + 10) * (n + 9) * (n + 8) * (n + 7) * (n + 6) * (n + 5) * (n + 4) * (n + 3) * (n + 2) * (n + 1) by ring]

        -- Consider all possible cases for n modulo 10
        mod_cases n % 10
        .
          replace H : n + 10 ≡ 0 + 10 [MOD 10]:= by exact Nat.ModEq.add_right 10 H
          simp at H
          replace H : 10 ∣ n + 10:= by exact Nat.dvd_of_mod_eq_zero H
          rcases H with ⟨k, hk⟩
          rw [hk]
          use (n + 9) * (n + 8) * (n + 7) * (n + 6) * (n + 5) * (n + 4) * (n + 3) * (n + 2) * (n + 1) * k
          ring
        .
          replace H : n + 9 ≡ 1 + 9 [MOD 10]:= by exact Nat.ModEq.add_right 9 H
          simp at H
          replace H : 10 ∣ n + 9:= by exact Nat.dvd_of_mod_eq_zero H
          rcases H with ⟨k, hk⟩
          rw [hk]
          use (n + 10) * (n + 8) * (n + 7) * (n + 6) * (n + 5) * (n + 4) * (n + 3) * (n + 2) * (n + 1) * k
          ring
        .
          replace H : n + 8 ≡ 2 + 8 [MOD 10]:= by exact Nat.ModEq.add_right 8 H
          simp at H
          replace H : 10 ∣ n + 8:= by exact Nat.dvd_of_mod_eq_zero H
          rcases H with ⟨k, hk⟩
          rw [hk]
          use (n + 10) * (n + 9) * (n + 7) * (n + 6) * (n + 5) * (n + 4) * (n + 3) * (n + 2) * (n + 1) * k
          ring
        .
          replace H : n + 7 ≡ 3 + 7 [MOD 10]:= by exact Nat.ModEq.add_right 7 H
          simp at H
          replace H : 10 ∣ n + 7:= by exact Nat.dvd_of_mod_eq_zero H
          rcases H with ⟨k, hk⟩
          rw [hk]
          use (n + 10) * (n + 9) * (n + 8) * (n + 6) * (n + 5) * (n + 4) * (n + 3) * (n + 2) * (n + 1) * k
          ring
        .
          replace H : n + 6 ≡ 4 + 6 [MOD 10]:= by exact Nat.ModEq.add_right 6 H
          simp at H
          replace H : 10 ∣ n + 6:= by exact Nat.dvd_of_mod_eq_zero H
          rcases H with ⟨k, hk⟩
          rw [hk]
          use (n + 10) * (n + 9) * (n + 8) * (n + 7) * (n + 5) * (n + 4) * (n + 3) * (n + 2) * (n + 1) * k
          ring
        .
          replace H : n + 5 ≡ 5 + 5 [MOD 10]:= by exact Nat.ModEq.add_right 5 H
          simp at H
          replace H : 10 ∣ n + 5:= by exact Nat.dvd_of_mod_eq_zero H
          rcases H with ⟨k, hk⟩
          rw [hk]
          use (n + 10) * (n + 9) * (n + 8) * (n + 7) * (n + 6) * (n + 4) * (n + 3) * (n + 2) * (n + 1) * k
          ring
        .
          replace H : n + 4 ≡ 6 + 4 [MOD 10]:= by exact Nat.ModEq.add_right 4 H
          simp at H
          replace H : 10 ∣ n + 4:= by exact Nat.dvd_of_mod_eq_zero H
          rcases H with ⟨k, hk⟩
          rw [hk]
          use (n + 10) * (n + 9) * (n + 8) * (n + 7) * (n + 6) * (n + 5) * (n + 3) * (n + 2) * (n + 1) * k
          ring
        .
          replace H : n + 3 ≡ 7 + 3 [MOD 10]:= by exact Nat.ModEq.add_right 3 H
          simp at H
          replace H : 10 ∣ n + 3:= by exact Nat.dvd_of_mod_eq_zero H
          rcases H with ⟨k, hk⟩
          rw [hk]
          use (n + 10) * (n + 9) * (n + 8) * (n + 7) * (n + 6) * (n + 5) * (n + 4) * (n + 2) * (n + 1) * k
          ring
        .
          replace H : n + 2 ≡ 8 + 2 [MOD 10]:= by exact Nat.ModEq.add_right 2 H
          simp at H
          replace H : 10 ∣ n + 2:= by exact Nat.dvd_of_mod_eq_zero H
          rcases H with ⟨k, hk⟩
          rw [hk]
          use (n + 10) * (n + 9) * (n + 8) * (n + 7) * (n + 6) * (n + 5) * (n + 4) * (n + 3) * (n + 1) * k
          ring
        .
          replace H : n + 1 ≡ 9 + 1 [MOD 10]:= by exact Nat.ModEq.add_right 1 H
          simp at H
          replace H : 10 ∣ n + 1:= by exact Nat.dvd_of_mod_eq_zero H
          rcases H with ⟨k, hk⟩
          rw [hk]
          use (n + 10) * (n + 9) * (n + 8) * (n + 7) * (n + 6) * (n + 5) * (n + 4) * (n + 3) * (n + 2) * k
          ring
      rcases h1 with ⟨t, ht⟩
      rcases hn with ⟨w, hw⟩
      rw [ht, hw]
      use t * w
      ring_nf
