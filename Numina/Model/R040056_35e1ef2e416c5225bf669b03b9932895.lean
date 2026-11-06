import Mathlib


theorem algebra_243199 (n : ℕ) :
    (Nat.card {k | ∃ a : ℝ, (Nat.choose n k) * (a ^ (n - k)) ≠ 0}) = n + 1 := by
  have h1 : {k : ℕ | ∃ a : ℝ, (Nat.choose n k) * (a ^ (n - k)) ≠ 0} = Set.Iic n := by
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_Iic]
    constructor
    · -- Assume k is in the left side
      intro hk
      rcases hk with ⟨a, ha⟩
      by_contra h
      push_neg at h
      -- Let's show that if k > n then (Nat.choose n k) = 0
      have h2 : Nat.choose n k = 0 := by
        apply Nat.choose_eq_zero_of_lt
        all_goals 
          omega
      -- Then (Nat.choose n k : ℝ) * (a ^ (n - k) : ℝ) = 0
      have h3 : (Nat.choose n k : ℝ) * (a ^ (n - k) : ℝ) = 0 := by
        rw [show (Nat.choose n k : ℝ) = (0 : ℝ) by exact_mod_cast h2]
        norm_num
      tauto
    · -- Show that if k ≤ n, then there exists an a such that (Nat.choose n k) * (a ^ (n - k)) ≠ 0
      intro hk
      use (1 : ℝ)
      have h2 : (Nat.choose n k : ℝ) > 0 := by
        have h3 : Nat.choose n k > 0 := by
          apply Nat.choose_pos 
          all_goals 
            omega
        positivity
      have h4 : (Nat.choose n k : ℝ) * (1 ^ (n - k) : ℝ) > 0 := by
        have h5 : (1 ^ (n - k) : ℝ) = 1 := by 
          simp 
        rw [h5]
        nlinarith
      positivity
  rw [h1]
  simp