import Mathlib

theorem number_theory_159620 (a n : ℤ) (_ : 1 ≤ a) (h₀ : a ∣ n + 2) (h₁ : a ∣ n^2 + n + 5) :
    a = 1 ∨ a = 7 := by
  have h2 : a ∣ 7 := by
    have h3 : a ∣ (n ^ 2 + n + 5 - (n - 1) * (n + 2)) := by
      apply Int.dvd_sub
      · -- $a \ | \ n^2 +n+5$ is h₁
        exact h₁
      · -- $a \ | \ (n - 1) \cdot (n + 2) $ since $a | n+2$ 
        have h4 : a ∣ (n - 1) * (n + 2) := by
          apply dvd_mul_of_dvd_right 
          exact h₀
        exact h4
    have h5 : n ^ 2 + n + 5 - (n - 1) * (n + 2) = 7 := by
      ring
    rw [h5] at h3
    exact h3
  have h3 : a ≤ 7 := by
    exact Int.le_of_dvd (show 0 < 7 by norm_num) h2
  interval_cases h4 : a <;> try { 
    tauto 
  } <;> try { tauto } <;> try { omega }
  <;> try { 
    tauto 
  } <;> try { tauto } <;> try { omega }
  <;> try { 
    tauto 
  } <;> try { tauto } <;> try { omega }