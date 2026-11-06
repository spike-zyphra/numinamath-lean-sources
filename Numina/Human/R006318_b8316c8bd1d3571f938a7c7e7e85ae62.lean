import Mathlib

/-Let $N$ be a positive integer. Show that there exist natural numbers $a$ and $b$ such that $a \neq b$, $a$ divides $b$, and $2a+b$ divides $Na$, if and only if $N \neq 1$ and $N \neq 3$.-/
theorem Number_Theory_635828 (N : ℕ) (hN : N > 0) :
  (∃ a b : ℕ, a ≠ b ∧ a ∣ b ∧ (2 * a + b) ∣ N * a) ↔ N ≠ 1 ∧ N ≠ 3 := by
  constructor
  · rintro⟨a, b, hne, hd1, hd2⟩
    -- First we prove the forward direction: if such a and b exist, then N ≠ 1 and N ≠ 3
    have : N ≠ 1 := by
      by_contra w
      rw [w] at hd2
      obtain ⟨k, hk⟩ := hd2
      -- We show that N≠1 by contradiction: if N=1, then (2a+b) ≤ a, which is impossible
      have : 2 * a + b ≤ 1 * a := by
        apply Nat.le_of_dvd
        by_contra w
        have : a = 0 := by omega
        simp [this] at hk hd1
        omega
        exact Dvd.intro k (Eq.symm hk)
      omega

    -- Similarly, we show that N≠3 by contradiction
    have : N ≠ 3 := by
      by_contra w
      rw [w] at hd2
      obtain ⟨k, hk⟩ := hd2
      -- We prove that if a>0, then k≤1, which leads to a contradiction
      have h1 : a > 0 := by
        by_contra w
        simp at w
        simp [w] at hk hd1
        omega
      have h2 : k ≤ 1 := by
        by_contra w
        have : 3 * a < (2 * a + b) * k := by
          calc
            3 * a < (2 * a + b) * 2 := by nlinarith
            _ ≤ (2 * a + b) * k := Nat.mul_le_mul_left (2 * a + b) (by linarith)
        omega

      -- We check k=0,1 and derive contradictions
      interval_cases k
      · omega
      · omega
    tauto

  -- Now we prove the backward direction: if N≠1 and N≠3, then such a and b exist
  · rintro ⟨hn1, hn3⟩
    by_cases h : N = 2
    · use 1, 0
      omega
    · have hn4 : N ≥ 4 := by omega
      -- For N≥4, we can use a=1 and b=N-2, which satisfy all required conditions
      use 1, N - 2
      exact ⟨(by omega), (by omega), (by use 1; omega)⟩
