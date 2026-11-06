import Mathlib

theorem number_theory_72548 (n : ℕ) (h : IsLeast {x | 0 < x ∧ (3 * x + 45) % 1060 = 16} n) :
    (18 * n + 17) % 1920 = 1043 := by
  have hn1 : 0 < n := h.left.left
  have hn2 : (3 * n + 45) % 1060 = 16 := h.left.right
  have h2 : ∀ m, 0 < m ∧ (3 * m + 45) % 1060 = 16 → m ≥ n := h.right
  have h3 : n ≤ 697 := by
    have h4 : (3 * 697 + 45) % 1060 = 16 := by norm_num
    have h5 : 0 < (697 : ℕ) := by norm_num
    have h6 : 697 ∈ {x | 0 < x ∧ (3 * x + 45) % 1060 = 16} := ⟨h5, h4⟩
    have h7 : n ≤ 697 := h2 697 h6
    exact h7
  have h4 : n ≥ 697 := by
    by_contra h'
    push_neg at h'
    have h8 : n < 697 := by omega
    -- Assume to the contrary n < 697, which must reach a contradiction
    have h9 : (3 * n + 45) % 1060 = 16 := hn2
    -- A contradiction would be obtained by proving that n must be greater than 697
    interval_cases n <;> norm_num at h9 hn1
    all_goals omega
  have hn : n = 697 := by omega
  -- At this point, the value of n is definitively known and to verify the congruence
  calc 
    (18 * n + 17) % 1920 = (18 * 697 + 17) % 1920 := by rw [hn]
    _ = 1043 := by norm_num