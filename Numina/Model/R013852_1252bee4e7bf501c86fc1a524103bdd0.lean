import Mathlib

theorem algebra_222552 {a : ℕ → ℝ} (ha1 : a 1 = 7 / 6)
    (hroots : ∀ n > 0, ∃ α β, α ≠ β ∧ a n * α^2 - a (n + 1) * α + 1 = 0 ∧
      a n * β^2 - a (n + 1) * β + 1 = 0 ∧ 6 * α - 2 * α * β + 6 * β = 3) :
    ∀ n, a n = 1 / 2 ^ n + 2 / 3 := by 
  have eq1 : ∀ n > 0, 6 * a (n + 1) - 2 = 3 * a n := by 
    intro n hn 
    obtain ⟨α, β, hneq, hα, hβ, h6⟩ := hroots n hn 
    have eq2 : a n * (α^2 - β^2) - a (n + 1) * (α - β) = 0 := by 
      nlinarith 
    have eq3 : α^2 - β^2 = (α - β) * (α + β) := by ring 
    rw [eq3] at eq2 
    have eq4 : (α - β : ℝ) ≠ 0 := by 
      exact sub_ne_zero_of_ne hneq 
    have eq5 : a n * (α + β) - a (n + 1) = 0 := by 
      apply (mul_left_inj' eq4).mp 
      linarith 
    have hprod : a n * (α * β) = 1 := by 
      nlinarith [sq_pos_of_ne_zero (show (α - β : ℝ) ≠ 0 by exact eq4), sq_nonneg (α + β), sq_nonneg (α - β)]
    have h7 : 6 * (α + β) - 2 * (α * β) = 3 := by 
      nlinarith 
    have eq9 : 6 * a (n + 1) - 2 = 3 * a n := by 
      have eq10 : a n * (α + β) = a (n + 1) := by linarith [eq5] 
      have eq11 : 6 * (a n * (α + β)) - 2 * (a n * (α * β)) = 3 * a n := by 
        have h8 : 6 * (α + β) - 2 * (α * β) = 3 := h7 
        calc 
          6 * (a n * (α + β)) - 2 * (a n * (α * β))
              = a n * (6 * (α + β) - 2 * (α * β)) := by ring 
          _ = a n * 3 := by rw [h8] 
          _ = 3 * a n := by ring 
      rw [eq10, hprod] at eq11 
      linarith 
    simpa using eq9 
  intro n 
  induction' n using Nat.strongRecOn with n ih 
  cases n with 
  | zero => 
    have ha0 : a 0 = 5 / 3 := by 
      have h2 := hroots 1 (by norm_num) 
      rcases h2 with ⟨α, β, hneq, hα, hβ, h6⟩ 
      simp [ha1] at hα hβ 
      have eq4 : (6 * a (1 + 1) - 2) = 3 * a 1 := by 
        specialize eq1 1 (by norm_num) 
        simpa using eq1 
      simp [ha1] at eq4 
      nlinarith [sq_pos_of_ne_zero (show (α - β : ℝ) ≠ 0 by 
        intro h 
        apply hneq 
        linarith 
      ), sq_nonneg (α - β), sq_nonneg (α + β)]
    rw [ha0]
    all_goals norm_num 
  | succ n => 
    cases n with 
    | zero => 
      rw [ha1] 
      all_goals norm_num 
    | succ n => 
      have ih_n1 := ih (n + 1) (by linarith) 
      have eq3 : a (n + 1 + 1) = (3 * a (n + 1) + 2) / 6 := by 
        have eq4 : (6 * a ( (n + 1) + 1 ) - 2) = 3 * a (n + 1) := by 
          specialize eq1 (n + 1) (by linarith) 
          simpa using eq1 
        linarith 
      rw [eq3, ih_n1] 
      field_simp 
      ring_nf