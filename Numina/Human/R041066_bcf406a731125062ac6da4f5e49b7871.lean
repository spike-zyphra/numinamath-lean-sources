import Mathlib

/- Let $a_{0}$ be a positive integer and $a_{n}=5 a_{n-1}+4$, for all $n \geq 1$. Can $a_{0}$ be chosen so that $a_{54}$ is a multiple of 2013?-/
theorem number_theory_605058 : ∃ a : ℕ → ℕ, (0 < a 0) ∧ (∀ n, a (n + 1) = 5 * a n + 4) ∧ 2013 ∣ a 54 := by
  -- It's clear that `2013` and `5^n` are coprime.
  have five_pow_co_2013 (n : ℕ) : Nat.Coprime 2013 (5 ^ n) := Nat.Prime.coprime_pow_of_not_dvd (by norm_num) (by norm_num)
  -- Let `b=5^54 % 2013`.
  set b := 5 ^ 54 % 2013 with hb
  -- Since `2013` and `5^n` are coprime, `b` is positive.
  have _ : 0 < b := by
    rw [Nat.pos_iff_ne_zero]
    intro h
    rw [h, eq_comm, ← Nat.dvd_iff_mod_eq_zero, Nat.gcd_eq_right_iff_dvd] at hb
    specialize five_pow_co_2013 54
    rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm] at five_pow_co_2013
    rw [five_pow_co_2013] at hb
    norm_num at hb
  -- `b` and `2013` are coprime.
  have b_co_2013 : Nat.Coprime 2013 b := by
    specialize five_pow_co_2013 54
    rw [← Nat.coprime_add_mul_right_right _ _ (5^54/2013)]
    have := Nat.div_add_mod (5 ^ 54) 2013
    rw [← hb, add_comm, mul_comm] at this
    rwa [this]
  -- Since `b` and `2013` are coprime, using Bezout's lemma, there exists
  -- `a+1` and `y` such that `(a + 1) * b = 2013 * y + 1`.
  have ⟨a0, ha0⟩ : ∃ a : ℕ, 0 < a ∧ ∃ y : ℤ, (a + 1) * b = 2013 * y + 1 := by
    have ⟨x, y, hxy⟩ : ∃ x y : ℤ, 1 = b * x + 2013 * y := by
      have := Nat.gcd_eq_gcd_ab b 2013
      rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm] at b_co_2013
      rw [b_co_2013] at this
      use b.gcdA 2013, b.gcdB 2013
      exact this
    have ⟨n, hn⟩ := Archimedean.arch (2 - x) (by norm_num : 0 < (2013 : ℤ))
    have hn' : 2 ≤ x + n * 2013 := by simp at hn; omega
    set a := x + n * 2013 - 1 with ha
    have hapos : 0 < a := by omega
    use a.natAbs
    refine ⟨by zify; rwa [abs_of_pos hapos], n * b - y, ?_⟩
    rw [Int.natCast_natAbs, abs_of_pos hapos, ha]
    linear_combination -hxy
  -- Let `a(n)=5^n(a+1)-1`.
  set a : ℕ → ℕ := fun n => 5 ^ n * (a0 + 1) - 1 with ha
  -- We need this lemma to perform natural number subtraction.
  have lem_1 (n : ℕ) : 1 ≤ 5 ^ n * (a0 + 1) := by
    have : 1 ≤ 5 ^ n := by exact Nat.one_le_pow' n 4
    have : 1 < a0 + 1 := by omega
    nlinarith
  use a
  -- By assumption`a(0)` is positivie.
  refine ⟨by simp [ha]; exact ha0.1, ?_, ?_⟩
  . -- Prove that `a(n+1)=5a(n)+4`
    intro n
    rw [ha]
    beta_reduce
    zify
    rw [Nat.cast_sub (lem_1 _), Nat.cast_sub (lem_1 _)]
    push_cast
    ring
  . -- Prove that `2013` divides `a(54)`
    rw [Nat.dvd_iff_mod_eq_zero, ha]
    beta_reduce
    apply Nat.sub_mod_eq_zero_of_mod_eq
    change _ ≡ 1 [MOD 2013]
    have h1 : 5 ^ 54 ≡ b [MOD 2013] := by exact Nat.ModEq.symm (Nat.mod_modEq (5 ^ 54) 2013)
    refine Nat.ModEq.trans (h1.mul_right (a0 + 1)) ?_
    rcases ha0 with ⟨_, y, hy⟩
    rw [mul_comm, Nat.ModEq]
    zify
    rw [hy, Int.add_emod]
    norm_num
