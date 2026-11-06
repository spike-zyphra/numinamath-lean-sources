import Mathlib

/- Prove that for any positive integer $ m$ there exist an infinite number of pairs of integers $(x,y)$ such that
$(\text{i})$ $x$ and $y$ are relatively prime;
$(\text{ii})$ $x$ divides $y^2+m;$
$(\text{iii})$ $y$ divides $x^2+m.$ -/

theorem number_theory_87165 (m : ℤ) (hm : m > 0):
    ∀ N: ℕ, ∃ x y : ℤ, y > N ∧ IsCoprime x y ∧ x ∣ y ^ 2 + m ∧ y ∣ x ^ 2 + m := by

    -- we prove a stronger statement: where we constrain the pairs $(x,y)$ to satisfy $x^2 - (m+2)xy + y^2 + m = 0$
    have h_strong: ∀ N: ℕ, ∃ x y: ℤ, y > N ∧ x ≤ y ∧ x ^ 2 - (m + 2) * x * y + y ^ 2 + m = 0 ∧
      IsCoprime x y ∧ x ∣ y ^ 2 + m ∧ y ∣ x ^ 2 + m := by
        intro N
        -- prove by induction
        induction' N with n hn
        -- base case: N = 0
        .
          use 1
          use 1
          norm_num
          ring
        -- inductive step: N = n + 1
        .
          obtain ⟨x, y, hy, hxy, h_eq, h_coprime, dx, dy⟩ := hn
          use y   -- we show that y, (m+2)y-x is what desired
          use (m + 2) * y - x
          have s1: (m + 2) * y - x > ↑(n + 1) := by
            simp
            nlinarith
          have s2: y ≤ (m + 2) * y - x := by nlinarith
          simp only [s1, s2]
          simp
          clear s1 s2
          constructor
          . -- show x' y' satisfy the equation
            nlinarith
          . -- show x' y' are coprime
            constructor
            .
              rw [isCoprime_comm]
              rw [← IsCoprime.neg_left_iff]
              rw [show -((m + 2) * y - x) = (-m - 2) * y + x by ring]
              apply IsCoprime.mul_add_right_left
              exact h_coprime

            .  -- show x' divides y'^2 + m
              constructor
              .
                rw [show ((m + 2) * y - x) ^ 2 + m = (y * ((m + 2) ^ 2 * y - 2 * x * (m + 2))) + (x ^ 2 + m) by ring]
                apply Int.dvd_add
                simp
                exact dy

              . -- show y' divides x'^2 + m
                have eq: y ^ 2 + m = x * ((m + 2) * y - x) := by nlinarith
                rw [eq]
                simp

    -- now we use the strong statement to prove the original statement
    intro N
    specialize h_strong N
    obtain ⟨x, y, hy, hxy, h_eq, h_coprime, dx, dy⟩ := h_strong
    use x
    use y
    