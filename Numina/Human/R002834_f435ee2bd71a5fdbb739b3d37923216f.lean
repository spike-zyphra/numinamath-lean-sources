import Mathlib

/-
4.1. The number $3^{2009}$ is represented as the sum of $k$ consecutive natural numbers. What is the greatest possible value of $k$?

Answer: 2 * 3 ^ 1004.
-/
theorem number_theory_119815 :
  IsGreatest { k : ℕ | ∃ a : ℕ, ∑ i ∈ Finset.Icc (a + 1) (a + k), i = 3 ^ 2009 } (2 * 3 ^ 1004) := by

  -- We prove a more general statement: For all positive integer $m$,
  -- $2 \cdot 3^m$ is the largest $k$ such that $3^(2m+1)$ can be represented
  -- as the sum of $k$ consecutive natural numbers.
  -- The origin statement then follows from setting $m = 1004$ since $2009 = 2(1004)+1$.
  suffices ∀ m, m > 0 →
    IsGreatest { k : ℕ | ∃ a : ℕ, ∑ i ∈ Finset.Icc (a + 1) (a + k), i = 3 ^ (2 * m + 1) }  (2 * 3 ^ m) by
    set h := this 1004 (by norm_num)
    have : 2 * 1004 + 1 = 2009 := by norm_num
    rw [this] at h
    exact h

  -- We claim that $\sum_{i=a+1}^{a+k} i = k(k+2a+1)$.
  -- The proof is by induction on $k$.
  have claim (a k : ℕ) : 2 * ∑ i ∈ Finset.Icc (a + 1) (a + k), i = k * (k + 2 * a + 1) := by
    induction k with
    | zero =>
      simp
    | succ k ih =>
      rw [show a + (k + 1) = a + k + 1 by omega]
      rw [Finset.sum_Icc_succ_top (by omega)]
      simp [mul_add] at ih ⊢
      rw [ih]
      ring_nf

  simp [IsGreatest, upperBounds]
  intro m hm
  constructor
  . -- We show that if $k = 2(3^m)$, then there exists $a$ such that
    -- $\sum_{i=a+1}^{a+k} i = 3^{2m + 1}$.

    -- Since $3^m - 1$ is even, there exists a natural number $r$ such that $3^m - 1 = 2r$.
    have : ∃ r, 3 ^ m - 1 = 2 * r := by
      suffices Even (3 ^ m - 1) by exact Even.exists_two_nsmul (3 ^ m - 1) this
      refine Nat.Odd.sub_odd ?_ ?_
      . refine Odd.pow ?_; decide
      . decide
    obtain ⟨ r, hr ⟩ := this

    -- It suffices to show that $2\sum_{i=r+1}^{r+2(3^m)} i = 2(3^{2m+1})$.
    suffices 2 * ∑ i ∈ Finset.Icc (r + 1) (r + 2 * 3 ^ m), i = 2 * 3 ^ (2 * m + 1) by
      use r
      have h : 0 < 2 := by norm_num
      apply Nat.mul_left_cancel h
      exact this

    -- By the claim, we have $2\sum_{i=r+1}^{r+2(3^m)} i = 2(3^m)(2(3^m) + 2r + 1)$.
    -- Simple alegbra finishes the proof.
    set s := claim r (2 * 3 ^ m)
    rw [s]
    rw [← hr]
    rw [add_assoc]
    rw [Nat.sub_add_cancel]
    . ring
    . apply Nat.one_le_pow'
  . intro k a
    -- We now show that if $a$ and $k$ are such that $\sum_{i=a+1}^{a+k} i = 3^{2m + 1}$,
    -- then $k \leq 2(3^m)$.

    -- By the claim, we have $2\sum_{i=a+1}^{a+k)} i = k(k + 2a + 1)$.
    set s := claim a k
    intro h
    rw [h] at s

    -- Since $2\sum_{i=a+1}^{a+k)} i = 3^{2m+1}$, we have
    -- $k^2 < k(k + 2a + 1) = 2(3^{2m+1})$.
    have h₀ : k ^ 2 < 2 * 3 ^ (2 * m + 1) := by
      calc
        _ = k * k := by rw [Nat.pow_two]
        _ < k * (k + 2 * a + 1) := by
             refine Nat.mul_lt_mul_of_pos_left ?_ ?_
             . linarith
             . by_contra g
               simp at g
               simp [g] at s
        _ = _ := by exact id (Eq.symm s)
    -- Sincee $k(k+2a+1) = 2(3^{2m+1})$, we have $k$ divides $2(3^{2m+1})$.
    have h₁ : k ∣ 2 * 3 ^ (2 * m + 1) := by exact Dvd.intro (k + 2 * a + 1) (id (Eq.symm s))

    -- We consider two cases, depending on whether or not $k$ and $2$ are coprime.
    by_cases g : Nat.Coprime k 2
    . -- If $k$ and $2$ are coprime, then $k$ divides $3^{2m+1}$.
      have h₃ : k ∣ 3 ^ (2 * m + 1) := by exact Nat.Coprime.dvd_of_dvd_mul_left g h₁

      -- Hence, there exists $p$ such that $k = 3^p$.
      have : ∃ p, p ≤ (2 * m + 1) ∧ k = 3 ^ p := by refine (Nat.dvd_prime_pow ?_).mp h₃; decide
      obtain ⟨ p, ⟨ hpl, hpr ⟩ ⟩ := this

      -- We can then show that $p \leq m$.
      rw [hpr] at h₀
      rw [← pow_mul] at h₀
      have h₃ : 3 ^ (p * 2) < 2 * 3 ^ (2 * m + 1) + 1 * 3 ^ (2 * m + 1) := by apply Nat.lt_add_right _ h₀
      have h₄ : 2 * 3 ^ (2 * m + 1) + 1 * 3 ^ (2 * m + 1) = 3 ^ (2*(m+1)) := by ring
      rw [h₄] at h₃
      rw [mul_comm] at h₃
      have h₅ : 2 * p < 2 * (m + 1) := by
        rw [pow_lt_pow_iff_right₀] at h₃
        . exact h₃
        . norm_num
      replace h₅ := Nat.lt_of_mul_lt_mul_left h₅
      replace h₅ := Nat.le_of_lt_succ h₅

      -- It suffices to show that $k^2 \leq (2(3^m))^2$.
      suffices k ^ 2 ≤ (2 * 3 ^ m ) ^ 2 by
        zify at this
        rw [sq_le_sq] at this
        norm_cast at this
      rw [hpr]
      rw [← pow_mul]
      -- Now, $k^2 = (3^(p \cdot 2)) \leq 3^(m \cdot 2) = (3^m)^2 \leq (2\cdot 3^m)^2 as desired.
      calc
        _ ≤ 3 ^ (m * 2) := by refine Nat.pow_le_pow_of_le ?_ ?_
                              . norm_num
                              . exact Nat.mul_le_mul_right 2 h₅
        _ = (3 ^ m) ^ 2 := by ring
        _ ≤ _ := by refine Nat.pow_le_pow_of_le_left ?_ 2
                    refine Nat.le_mul_of_pos_left (3 ^ m) ?_
                    norm_num
    . -- Suppose the $k$ and $2$ are not coprime.
      simp at g
      -- Then there exists a natural number $z$ such
      -- $k = 2z$.
      obtain ⟨ z, hz ⟩ := g
      rw [← two_mul] at hz
      rw [hz] at h₁ ⊢

      -- It suffices to show that $z \leq 3^m$.
      suffices z ≤ 3 ^ m by exact Nat.mul_le_mul_left 2 this
      -- Since $k$ divides $2(3^{2m+1})$, we have $2z$ divides $2(3^{2 * m + 1}$.
      -- Thus $z$ divides $3^{2 * m + 1}$.
      rw [mul_dvd_mul_iff_left] at h₁
      . -- Hence, there exists $p$ such that $z = 3^p$.
        have : ∃ p, p ≤ (2 * m + 1) ∧ z = 3 ^ p := by refine (Nat.dvd_prime_pow ?_).mp h₁; decide
        obtain ⟨ p, ⟨ hpl, hpr ⟩ ⟩ := this
        rw [hz] at h₀
        rw [hpr] at h₀ ⊢

        -- Hence, we need to show that $3^p \leq 3^m$.
        -- It suffices to show that $p \leq m$.
        suffices p ≤ m by refine Nat.pow_le_pow_of_le ?_ this; norm_num

        -- Suppose by way of contradiction that $p > m$.
        by_contra g
        simp at g
        -- That is, $m + 1 leq p$.
        have : m + 1 ≤ p := by exact g

        -- We show that $2(3^{2m+1} ≤ (2(3^p))^2$.
        -- This follows from direct calculation.
        revert h₀
        simp
        calc
          _ ≤ 3 * 3 ^ (2 * m + 1) := by apply Nat.mul_le_mul_right; norm_num
          _ = 3 ^ (2 * (m + 1)) := by ring
          _ ≤ 3 ^ (2 * p) := by refine Nat.pow_le_pow_of_le ?_ ?_
                                . norm_num
                                . linarith
          _ ≤ _ := by rw [mul_comm, pow_mul]
                      refine Nat.pow_le_pow_of_le_left ?_ 2
                      refine Nat.le_mul_of_pos_left (3 ^ p) ?_
                      norm_num
      . norm_num