import Mathlib

theorem number_theory_149067 (x : ℤ) (p m n : ℕ) (hp : p > 0) (hm : m > 0) (hn : n > 0) :
    (x^2 + x + 1) ∣ (x^(3 * p) + x^(3 * m + 1) + x^(3 * n + 2)) := by
  have h1 : (x ^ 2 + x + 1) ∣ (x ^ 3 - 1) := by
    use (x - 1)
    ring
  have h2 : (x ^ 2 + x + 1) ∣ (x ^ (3 * p) + x ^ (3 * m + 1) + x ^ (3 * n + 2) - (1 + x + x ^ 2)) := by
    have h21 : (x ^ 2 + x + 1) ∣ (x ^ (3 * p) - 1) := by
      have h3 : ∀ (k : ℕ), (x ^ 2 + x + 1) ∣ ((x ^ 3) ^ k - 1) := by
        intro k
        induction k with
        | zero => 
          norm_num
        | succ k ih => 
          have h5 : (x ^ 2 + x + 1) ∣ ((x ^ 3) ^ (k + 1) - 1) := by
            have h4 : (x ^ 3) ^ (k + 1) - 1 = ((x ^ 3) ^ k) * (x ^ 3) - 1 := by ring
            rw [h4]
            have h7 : ((x ^ 3) ^ k) * (x ^ 3) - 1 = ((x ^ 3) ^ k - 1) + ((x ^ 3) ^ k * (x ^ 3 - 1)) := by
              nlinarith
            rw [h7]
            apply Dvd.dvd.add
            · exact ih
            · 
              apply Dvd.dvd.mul_left
              exact h1
          exact h5
      specialize h3 p
      have h21 : (x ^ 3) ^ p - 1 = x ^ (3 * p) - 1 := by
        have h20 : (x ^ 3) ^ p = x ^ (3 * p) := by
          ring_nf
        rw [h20]
      rw [h21] at h3
      exact h3
    have h22 : (x ^ 2 + x + 1) ∣ (x ^ (3 * m + 1) - x) := by
      have h33 : (x ^ 2 + x + 1) ∣ (x ^ (3 * m + 1) - x) := by
        have h44 : x ^ (3 * m + 1) - x = x * (x ^ (3 * m) - 1) := by
          ring
        rw [h44]
        apply Dvd.dvd.mul_left
        have h31 : (x ^ 2 + x + 1) ∣ (x ^ (3 * m) - 1) := by
          have h33 : (x ^ 2 + x + 1) ∣ ((x ^ 3) ^ m - 1) := by
            have h30 : ∀ (k : ℕ), (x ^ 2 + x + 1) ∣ ((x ^ 3) ^ k - 1) := by
              intro k
              induction k with
              | zero => 
                norm_num
              | succ k ih => 
                have h5 : (x ^ 2 + x + 1) ∣ ((x ^ 3) ^ (k + 1) - 1) := by
                  have h4 : (x ^ 3) ^ (k + 1) - 1 = ((x ^ 3) ^ k) * (x ^ 3) - 1 := by ring
                  rw [h4]
                  have h7 : ((x ^ 3) ^ k) * (x ^ 3) - 1 = ((x ^ 3) ^ k - 1) + ((x ^ 3) ^ k * (x ^ 3 - 1)) := by
                    nlinarith
                  rw [h7]
                  apply Dvd.dvd.add
                  · exact ih
                  · 
                    apply Dvd.dvd.mul_left
                    exact h1
                exact h5
            specialize h30 m
            simpa using h30
          have h32 : (x ^ 3) ^ m - 1 = x ^ (3 * m) - 1 := by
            have h20 : (x ^ 3) ^ m = x ^ (3 * m) := by
              ring_nf
            rw [h20]
          rw [h32] at h33
          exact h33
        exact h31
      exact h33
    have h23 : (x ^ 2 + x + 1) ∣ (x ^ (3 * n + 2) - x ^ 2) := by
      have h40 : x ^ (3 * n + 2) - x ^ 2 = x ^ 2 * (x ^ (3 * n) - 1) := by
        ring_nf
      rw [h40]
      apply Dvd.dvd.mul_left
      have h31 : (x ^ 2 + x + 1) ∣ (x ^ (3 * n) - 1) := by
        have h33 : (x ^ 2 + x + 1) ∣ ((x ^ 3) ^ n - 1) := by
          have h30 : ∀ (k : ℕ), (x ^ 2 + x + 1) ∣ ((x ^ 3) ^ k - 1) := by
            intro k
            induction k with
            | zero => 
              norm_num
            | succ k ih => 
              have h5 : (x ^ 2 + x + 1) ∣ ((x ^ 3) ^ (k + 1) - 1) := by
                have h4 : (x ^ 3) ^ (k + 1) - 1 = ((x ^ 3) ^ k) * (x ^ 3) - 1 := by ring
                rw [h4]
                have h7 : ((x ^ 3) ^ k) * (x ^ 3) - 1 = ((x ^ 3) ^ k - 1) + ((x ^ 3) ^ k * (x ^ 3 - 1)) := by
                  nlinarith
                rw [h7]
                apply Dvd.dvd.add
                · exact ih
                · 
                  apply Dvd.dvd.mul_left
                  exact h1
              exact h5
          specialize h30 n
          simpa using h30
        have h32 : (x ^ 3) ^ n - 1 = x ^ (3 * n) - 1 := by
          have h20 : (x ^ 3) ^ n = x ^ (3 * n) := by
            ring_nf
          rw [h20]
        rw [h32] at h33
        exact h33
      exact h31
    have h34 : (x ^ 2 + x + 1) ∣ ((x ^ (3 * p) + x ^ (3 * m + 1) + x ^ (3 * n + 2)) - (1 + x + x ^ 2)) := by
      have h35 : (x ^ (3 * p) + x ^ (3 * m + 1) + x ^ (3 * n + 2)) - (1 + x + x ^ 2) = (x ^ (3 * p) - 1) + (x ^ (3 * m + 1) - x) + (x ^ (3 * n + 2) - x ^ 2) := by 
        ring
      rw [h35]
      apply Dvd.dvd.add
      · apply Dvd.dvd.add
        · exact h21
        · exact h22
      · exact h23
    exact h34
  have h35 : (x ^ 2 + x + 1) ∣ (x ^ (3 * p) + x ^ (3 * m + 1) + x ^ (3 * n + 2)) := by
    have h30 : (x ^ (3 * p) + x ^ (3 * m + 1) + x ^ (3 * n + 2)) = (x ^ (3 * p) + x ^ (3 * m + 1) + x ^ (3 * n + 2) - (1 + x + x ^ 2)) + (1 + x + x ^ 2) := by
      ring
    rw [h30]
    apply Dvd.dvd.add
    · exact h2
    · 
      use 1
      all_goals ring
  exact h35