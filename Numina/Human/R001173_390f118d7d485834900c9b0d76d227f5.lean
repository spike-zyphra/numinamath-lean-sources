import Mathlib

/-A particular geometric sequence has strictly decreasing terms. After the first term, each successive term is calculated by multiplying the previous term by $\frac{m}{7}$. If the first term of the sequence is positive, how many possible integer values are there for $m$?-/
theorem algebra_20851 : {m : ℤ | ∃ a : ℕ → ℝ, 0 < a 0 ∧ ∀ n, a n = a 0 * (m / 7)^n ∧ a (n + 1) < a n}.ncard = 6 := by
  -- suffices to show that the set is {1, 2, 3, 4, 5, 6}.
  suffices {m : ℤ | ∃ a : ℕ → ℝ, 0 < a 0 ∧ ∀ n, a n = a 0 * (m / 7)^n ∧ a (n + 1) < a n} = {1, 2, 3, 4, 5, 6} by
    simp [this]
    norm_num
  ext m
  simp
  constructor <;> intro h 
  · obtain ⟨a, a0pos, ha⟩ := h 
    obtain ⟨han, dec⟩ := forall_and.1 ha
    -- By the hypothesis, we have `a 1 = a 0 * m / 7`, `a 2 = a 0 * (m / 7)^2`, `a 1 < a 0` and `a 2 < a 1`. 
    have ha1 := han 1 
    have ha2 := han 2
    have a1lt := dec 0
    have a2lt := dec 1
    -- So we get $0 < m < 7$, i.e. m = 1, 2, 3, 4, 5 or 6.
    simp [ha1, ha2] at a1lt a2lt 
    have mpos : (0 : ℝ) < m := by nlinarith
    have mlt7 : m < (7 : ℝ) := by nlinarith
    norm_cast at mpos mlt7 
    interval_cases m <;> tauto
  · -- Verify that when m = 1, 2, 3, 4, 5, or 6, we always get a strictly decreasing sequence a n = (m / 7)^n.
    let a : ℕ → ℝ:= fun n => (m / 7)^n
    use a 
    simp [a]
    intro n 
    rw [pow_add]
    nth_rw 2 [← mul_one (((m : ℝ) / 7)^n)]
    rcases h with h | h | h | h | h | h 
    <;> apply (mul_lt_mul_left (by positivity )).2 
    <;> norm_num [h]   