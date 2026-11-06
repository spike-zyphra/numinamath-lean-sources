import Mathlib

theorem number_theory_311220 (a b c : ℚ) (h₀ : a ≠ b) (h₁ : b ≠ c) (h₂ : a ≠ c)
    (h₃ : abs (a - b) + abs (b - c) = abs (a - c)) :
    (a < b ∧ b < c) ∨ (c < b ∧ b < a) := by
  by_cases h1 : a - b ≥ 0
  · -- In this case, $a \geq b$ so $|a-b| = a-b$
    rw [abs_of_nonneg h1] at h₃
    by_cases h2 : b - c ≥ 0
    · -- In this case, $b \geq c$ so $|b-c| = b-c$
      rw [abs_of_nonneg h2] at h₃
      -- Now $a - b + b - c = a - c = |a-c|$
      -- Since $a \geq b \geq c$ and all are distinct
      -- we get $a > b > c$ which proves $c < b < a$
      right
      have h4 : a > b := by
        by_contra h
        push_neg at h
        have : a = b := by linarith
        contradiction
      have h5 : b > c := by
        by_contra h
        push_neg at h
        have : b = c := by linarith
        contradiction
      exact ⟨by linarith, by linarith⟩
    · -- In this case, $b < c$ so $|b-c| = c-b$
      rw [abs_of_neg (lt_of_not_ge h2)] at h₃
      by_cases h3 : a - c ≥ 0
      · -- In this case, $a \geq c$ so $|a-c| = a-c$
        rw [abs_of_nonneg h3] at h₃
        exfalso
        have h12 : b = c := by linarith
        contradiction
      · -- In this case, $a < c$ so $|a-c| = c-a$
        rw [abs_of_neg (lt_of_not_ge h3)] at h₃
        exfalso
        have h12 : a = b := by linarith
        contradiction
  · -- In this case, $a < b$ so $|a-b| = b-a$
    rw [abs_of_neg (lt_of_not_ge h1)] at h₃
    by_cases h2 : b - c ≥ 0
    · -- In this case, $b \geq c$ so $|b-c| = b-c$
      rw [abs_of_nonneg h2] at h₃
      by_cases h3 : a - c ≥ 0
      · -- In this case, $a \geq c$ so $|a-c| = a-c$
        rw [abs_of_nonneg h3] at h₃
        exfalso
        have h12 : b = a := by linarith
        have h23 : (a : ℚ) < b := by nlinarith
        linarith
      · -- In this case, $a < c$ so $|a-c| = c-a$
        rw [abs_of_neg (lt_of_not_ge h3)] at h₃
        exfalso
        have h12 : b = c := by linarith
        contradiction
    · -- In this case, $b < c$ so $|b-c| = c-b$
      rw [abs_of_neg (lt_of_not_ge h2)] at h₃
      -- We have $|a-b| + |b-c| = |a-c| = b-a + c-b = c-a$
      -- Since $a < c$ so $|a-c| = c-a$
      -- This gives $a < b < c$
      left
      have h4 : a < b := by linarith
      have h5 : b < c := by linarith
      exact ⟨by linarith, by linarith⟩