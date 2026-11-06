import Mathlib

/-
Let $A$ be a 4 -digit integer. When both the first digit (left-most) and the third digit are increased by $n$, and the second digit and the fourth digit are decreased by $n$, the new number is $n$ times $A$. Find the value of $A$.
-/
theorem number_theory_100932 (a b c d n A : ℕ)
  (ha : a ∈ Finset.Icc 1 9)
  (hb : b ∈ Finset.range 10)
  (hc : c ∈ Finset.range 10)
  (hd : d ∈ Finset.range 10)
  (hA : A = 1000 * a + 100 * b + 10 * c + d) -- A is a four-digit number
  (hn : n ∈ Finset.Icc 1 9 ∧ n ≤ b ∧ n ≤ d) -- n is a digit that alters A and can be subtracted from b and d
  (h : 1000 * (a + n) + 100 * (b - n) + 10 * (c + n) + (d - n) = n * A) : A = 1818 := by

  -- Using that $A = \overline{abcd}$, the equation
  -- $1000(a + n) + 100(b - n) + 10(c + n) + (d - n) = nA$ simplifies to $A + 909n = nA$
  have h₀ : A + 909 * n = n * A := by
    simp [mul_add, Nat.mul_sub] at h
    rw [← h, hA]
    symm
    calc
          1000 * a + 1000 * n + (100 * b - 100 * n) + (10 * c + 10 * n) + (d - n)
        = 1000 * a + (1000 * n + (100 * b - 100 * n)) + (10 * c + (10 * n + (d - n))) := by ring_nf
      _ = 1000 * a + (1000 * n + 100 * b - 100 * n) + (10 * c + (10 * n + (d - n))) := by
           rw [Nat.add_sub_assoc]
           omega
      _ = 1000 * a + (100 * b + 1000 * n - 100 * n) + (10 * c + (10 * n + (d - n))) := by rw [add_comm (1000 * n)]
      _ = 1000 * a + (100 * b + (1000 * n - 100 * n)) + (10 * c + (10 * n + (d - n))) := by
           rw [Nat.add_sub_assoc]
           omega
      _ = 1000 * a + (100 * b + (1000 * n - 100 * n)) + (10 * c + (10 * n + d - n)) := by
           rw [Nat.add_sub_assoc]
           omega
      _ = 1000 * a + (100 * b + (1000 * n - 100 * n)) + (10 * c + (d + 10 * n - n)) := by rw [add_comm (10 * n)]
      _ = 1000 * a + (100 * b + (1000 * n - 100 * n)) + (10 * c + (d + (10 * n - n))) := by
           rw [Nat.add_sub_assoc]
           omega
      _ = 1000 * a + (100 * b + (1000 * n - 100 * n)) + (10 * c + (d + (10 * n - 1 * n))) := by rw [one_mul]
      _ = 1000 * a + (100 * b + (1000 - 100) * n) + (10 * c + (d + (10 - 1) * n )) := by
           rw [Nat.sub_mul, Nat.sub_mul]
      _ = _ := by simp; ring

  -- It follows that $(n-1)A = 909n$.
  have h₂ : (n - 1) * A = 909 * n := by
    rw [Nat.sub_mul]
    rw [← h₀, one_mul]
    rw [add_comm]
    simp

  -- We show that $n = 2$ or $n = 4$.
  have h₁ : n = 2 ∨ n = 4 := by
    simp at hn
  -- We divide into two cases depending on whether or or $n \leq 2$.
    by_cases g : n ≤ 2
    . -- Suppose that $n \leq 2$.
      by_cases g' : n = 2
      . -- If $n = 2$, then we are done.
        left
        exact g'
      . -- Otherwise, $n = 1$.
        -- Substituting for $n$ in $(n-1) A = 909n$ gives a contradiction.
        have : n = 1 := by omega
        simp [this] at h₂
    . -- Suppose that it is not true that $n \leq 2$.
      -- That is, $2 < n$.
      simp at g

      -- Note that $n - 1$ and $n$ are coprime.
      have h₃ : Nat.Coprime (n - 1) n := by
        refine (Nat.coprime_self_sub_left ?_).mpr ?_
        . omega
        . apply Nat.gcd_one_left

      -- Since $(n-1)A = 909n$, we have that $n-1$ divides 909.
      have h₄ : (n - 1) ∣ 909 := by
        rw [← Nat.Coprime.dvd_mul_right h₃]
        rw [← h₂]
        apply Nat.dvd_mul_right

      -- But $909 = 9 \cdot 101$.
      have h₅ : 909 = 9 * 101 := by norm_num
      rw [h₅] at h₄

      -- Since $101$ is prime and $2 \leq n-1 < 10$,
      -- we must have that $n-1$ and 101 are coprime.
      have h₆ : Nat.Coprime (n - 1) 101 := by
        apply Nat.Coprime.symm
        apply Nat.coprime_of_lt_prime
        . omega
        . omega
        . decide

      -- Thus, $n-1$ divides 9.
      have h₇ : (n - 1) ∣ 9 := by
        rw [← Nat.Coprime.dvd_mul_right h₆]
        exact h₄

      -- But, $9 = 3^2$.
      have h₈ : 9 = 3 ^ 2 := by rfl
      rw [h₈] at h₇
      rw [Nat.dvd_prime_pow] at h₇

      -- Since 3 is prime, we must have
      -- $n-1=1$, or $n-1=3$ or $n-1=9$
      -- Only $n-1=3$ is possible.
      -- Hence, $n=4$.
      right
      . obtain ⟨ k, ⟨ hkl, hkr ⟩ ⟩ := h₇
        by_cases g' : k ≤ 1
        . by_cases g'' : k = 0
          . simp [g''] at hkr
            omega
          . have : k = 1 := by omega
            simp [this] at hkr
            exact hkr
        . have : k = 2 := by omega
          simp [this] at hkr
          rw [hkr]
          omega
      . exact Nat.prime_three

  obtain g | g := h₁
  . -- Suppose that $n=2$.
    -- This gives $A=1818$ as desired.
    rw [g] at h₀
    simp at h₀
    rw [two_mul] at h₀
    exact Nat.add_left_cancel (id (Eq.symm h₀))
  . -- Suppose that $n=4$.
    -- This gives $A=1212$.
    rw [g] at h₀
    simp at h₀
    have : 3 * A = 3 * 1212 := by
      have : 4 * A = A + 3 * A := by ring
      rw [this] at h₀
      simp
      exact Eq.symm (Nat.add_left_cancel h₀)
    have : A = 1212 := by apply @Nat.mul_left_cancel 3 A 1212
                          . norm_num
                          . exact this
    -- But this means $b=2$.
    have : b = 2 := by
      rw [this] at hA
      have : a = 1 := by
        by_cases g : a > 1
        . have : ∃ r, a = 2 + r := by exact Nat.exists_eq_add_of_le g
          obtain ⟨ r, hr ⟩ := this
          rw [hr] at hA
          omega
        . simp at g
          simp at ha
          omega
      omega
    -- Since $n=4$, we have $b < n$, contradicting our assumption.
    by_contra
    omega