import Mathlib

/-5. For the positive integer $n$, define $a_{n}$ as the unit digit of $n^{(n+1)^{n+2}}$. Then $\sum_{n=1}^{2018} a_{n}=$ $\qquad$ .-/
theorem number_theory_248298 {a : ℕ → ℕ} (ha : ∀n, a n = (n ^ ((n + 1) ^ (n + 2))) % 10) : ∑ n in Finset.Icc 1 2018, a n = 5857 := by
  have h₂ : a = λ n ↦ [0,1,2,1,4,5,6,1,8,1].getD (n % 10) 0 := by
    ext n
    obtain ⟨k, r, hn₁, hr₁⟩ := show ∃k r, n = 10 * k + r ∧ r < 10 by
      use n/10, n%10
      omega
    rw [show n % 10 = r by omega]
    have h₁ : a n = a n % 10 := by
      rw [ha]
      omega
    rw [h₁]
    obtain (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 := by omega
    · -- r = 0
      norm_num at hn₁
      have : ∀m ≥ 1, n^m % 10 = 0 := by
        intro m hm₁
        apply Nat.dvd_iff_mod_eq_zero.mp
        rw [hn₁]
        apply Dvd.dvd.pow (by simp) (by omega)
      rw [ha, this]
      simp
      exact Nat.one_le_pow' (n + 2) n
    · -- r = 1
      have : ∀m ≥ 1, n^m % 10 = 1 := by
        intro m hm₁
        rw [hn₁, Nat.pow_mod, show (10 * k + 1) % 10 = 1 by omega]
        simp
      rw [ha, this]
      simp
      exact Nat.one_le_pow' (n + 2) n
    · -- r = 2
      obtain ⟨q, hq₁⟩ := show ∃q, (n + 1) ^ (n + 2) = 4 * q + 1 by
        suffices (n + 1) ^ (n + 2) % 4 = 1 by
          use (n + 1) ^ (n + 2) / 4
          omega
        rw [hn₁, Nat.pow_mod]
        by_cases hk₁: k % 2 = 0
        · rw [show (10 * k + 2 + 1) % 4 = 3 by omega]
          rw [show 10 * k + 2 + 2 = 10 * k + 4 by omega]
          rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod]
          norm_num
        rw [show (10 * k + 2 + 1) % 4 = 1 by omega]
        norm_num
      rw [ha, hq₁, hn₁, Nat.pow_mod, show (10 * k + 2) % 10 = 2 by omega]
      simp
      rw [Nat.pow_add_one, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod]
      simp
      have : ∀m, 6^m * 2 % 10 = 2 := by
        intro m
        induction' m using Nat.strongRec with m hm
        by_cases hm₂ : m = 0
        · rw [hm₂]
          simp
        specialize hm (m - 1) (by omega)
        rw [show m = m - 1 + 1 by omega, Nat.pow_add_one, Nat.mul_mod]
        omega
      apply this
    · -- r = 3
      obtain ⟨q, hq₁⟩ := show ∃q, (n + 1) ^ (n + 2) = 4 * q by
        suffices (n + 1) ^ (n + 2) % 4 = 0 by
          use (n + 1) ^ (n + 2) / 4
          omega
        rw [hn₁, Nat.pow_mod]
        by_cases hk₁: k % 2 = 0
        · rw [show (10 * k + 3 + 1) % 4 = 0 by omega]
          simp
        rw [show (10 * k + 3 + 1) % 4 = 2 by omega]
        rw [show 10 * k + 3 + 2 = 10 * k + 5 by omega]
        rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod]
        norm_num
      rw [ha, hq₁, hn₁, Nat.pow_mod, show (10 * k + 3) % 10 = 3 by omega]
      simp
      rw [Nat.pow_mul, Nat.pow_mod]
      simp
    · -- r = 4
      obtain ⟨q, hq₁⟩ := show ∃q, (n + 1) ^ (n + 2) = 4 * q + 1 by
        suffices (n + 1) ^ (n + 2) % 4 = 1 by
          use (n + 1) ^ (n + 2) / 4
          omega
        rw [hn₁, Nat.pow_mod]
        by_cases hk₁: k % 2 = 0
        · rw [show (10 * k + 4 + 1) % 4 = 1 by omega]
          simp
        rw [show (10 * k + 4 + 1) % 4 = 3 by omega]
        rw [show 10 * k + 4 + 2 = 10 * k + 6 by omega]
        rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod]
        norm_num
      rw [ha, hq₁, hn₁, Nat.pow_mod, show (10 * k + 4) % 10 = 4 by omega]
      simp
      rw [Nat.pow_add_one, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod]
      simp
      have : ∀m, 6^m * 4 % 10 = 4 := by
        intro m
        induction' m using Nat.strongRec with m hm
        by_cases hm₂ : m = 0
        · rw [hm₂]
          simp
        specialize hm (m - 1) (by omega)
        rw [show m = m - 1 + 1 by omega, Nat.pow_add_one, Nat.mul_mod]
        omega
      apply this
    · -- r = 5
      have : ∀m ≥ 1, n^m % 10 = 5 := by
        intro m hm₁
        rw [hn₁, Nat.pow_mod, show (10 * k + 5) % 10 = 5 by omega]
        suffices 10 ∣ 5^m - 5 by
          obtain ⟨p, hp⟩ := this
          have : 5^m = 10 * p + 5 := by
            rw [←hp, Eq.comm]
            apply Nat.sub_add_cancel
            apply Nat.le_self_pow ?_ 5
            omega
          rw [this]
          omega
        have : 5^m - 5 = 5 * (5^(m - 1) - 1) := by
          rw [Nat.mul_sub, mul_comm, ←Nat.pow_add_one]
          rw [show m - 1 + 1 = m by omega]
        rw [this, show 10 = 5 * 2 by norm_num]
        apply Nat.mul_dvd_mul_left 5
        suffices Even (5^(m - 1) - 1) by exact even_iff_two_dvd.mp this
        rw [Nat.even_sub']
        norm_num
        apply Odd.pow
        native_decide
        exact Nat.one_le_pow' (m - 1) 4
      rw [ha, this]
      simp
      exact Nat.one_le_pow' (n + 2) n
    · -- r = 6
      have : ∀m ≥ 1, n^m % 10 = 6 := by
        intro m hm₁
        rw [hn₁, Nat.pow_mod, show (10 * k + 6) % 10 = 6 by omega]
        induction' m using Nat.strongRec with m hm
        by_cases hm₂ : m = 1
        · rw [hm₂]
        specialize hm (m - 1) (by omega) (by omega)
        rw [show m = m - 1 + 1 by omega, Nat.pow_add_one, Nat.mul_mod, hm]
      rw [ha, this]
      simp
      exact Nat.one_le_pow' (n + 2) n
    · -- r = 7
      obtain ⟨q, hq₁⟩ := show ∃q, (n + 1) ^ (n + 2) = 4 * q by
        suffices (n + 1) ^ (n + 2) % 4 = 0 by
          use (n + 1) ^ (n + 2) / 4
          omega
        rw [hn₁, Nat.pow_mod]
        by_cases hk₁: k % 2 = 0
        · rw [show (10 * k + 7 + 1) % 4 = 0 by omega]
          simp
        rw [show (10 * k + 7 + 1) % 4 = 2 by omega]
        rw [show 10 * k + 7 + 2 = 10 * k + 9 by omega]
        rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod]
        norm_num
      rw [ha, hq₁, hn₁, Nat.pow_mod, show (10 * k + 7) % 10 = 7 by omega]
      simp
      rw [Nat.pow_mul, Nat.pow_mod]
      simp
    · -- r = 8
      obtain ⟨q, hq₁⟩ := show ∃q, (n + 1) ^ (n + 2) = 4 * q + 1 by
        suffices (n + 1) ^ (n + 2) % 4 = 1 by
          use (n + 1) ^ (n + 2) / 4
          omega
        rw [hn₁, Nat.pow_mod]
        by_cases hk₁: k % 2 = 0
        · rw [show (10 * k + 8 + 1) % 4 = 1 by omega]
          simp
        rw [show (10 * k + 8 + 1) % 4 = 3 by omega]
        rw [show 10 * k + 8 + 2 = 10 * k + 10 by omega]
        rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod]
        norm_num
      rw [ha, hq₁, hn₁, Nat.pow_mod, show (10 * k + 8) % 10 = 8 by omega]
      simp
      rw [Nat.pow_add_one, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod]
      simp
      have : ∀m, 6^m * 8 % 10 = 8 := by
        intro m
        induction' m using Nat.strongRec with m hm
        by_cases hm₂ : m = 0
        · rw [hm₂]
          simp
        specialize hm (m - 1) (by omega)
        rw [show m = m - 1 + 1 by omega, Nat.pow_add_one, Nat.mul_mod]
        omega
      apply this
    · -- r = 9
      obtain ⟨q, hq₁⟩ := show ∃q, (n + 1) ^ (n + 2) = 4 * q by
        suffices (n + 1) ^ (n + 2) % 4 = 0 by
          use (n + 1) ^ (n + 2) / 4
          omega
        rw [hn₁, Nat.pow_mod]
        by_cases hk₁: k % 2 = 0
        · rw [show (10 * k + 9 + 1) % 4 = 2 by omega]
          rw [show 10 * k + 9 + 2 = 10 * k + 11 by omega]
          rw [Nat.pow_add, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod]
          norm_num
        rw [show (10 * k + 9 + 1) % 4 = 0 by omega]
        simp
      rw [ha, hq₁, hn₁, Nat.pow_mod, show (10 * k + 9) % 10 = 9 by omega]
      simp
      rw [Nat.pow_mul, Nat.pow_mod]
      simp
  rw [h₂]
  simp
  native_decide
