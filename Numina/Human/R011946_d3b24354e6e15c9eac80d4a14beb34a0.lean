import Mathlib
open  Real Finset  

/-A polynomial $f$ with integer coefficients is written on the blackboard. The teacher is a mathematician who has $3$ kids: Andrew, Beth and Charles. Andrew, who is $7$, is the youngest, and Charles is the oldest. When evaluating the polynomial on his kids' ages he obtains:
[list]$f(7) = 77$
$f(b) = 85$, where $b$ is Beth's age,
$f(c) = 0$, where $c$ is Charles' age.[/list]
How old is each child?-/
theorem algebra_73510 {f : Polynomial ℤ}(b c : ℤ) (hf : f.eval 7 = 77) (hb : f.eval b = 85) (hc : f.eval c = 0)
    (hord : 7 < b ∧ b < c) :
  b = 9 ∧ c = 14 := by
  -- Use the property of integer coefficient polynomials $p - q ∣ f(p) - f(q)$.
  -- Compute $b - 7 ∣ f(b) - f(7) = 85 - 77 = 8$.
  have h_b_minus_7_div : (b - 7 : ℤ) ∣ (f.eval b - f.eval 7) := by
    apply Polynomial.sub_dvd_eval_sub
  have h_b_minus_7_vals : (b - 7 : ℤ) ∈ ({1, 2, 4, 8} : Finset ℤ) := by
    have h_diff : f.eval b - f.eval 7 = 85 - 77 := by rw [hb, hf]
    have h_diff_val : f.eval b - f.eval 7 = 8 := by norm_num [h_diff]
    have h_b_minus_7_pos : b - 7 > 0 := by nlinarith [hord.1]
    have h_divisors : (b - 7 : ℤ) ∣ 8 := by
      rw [h_diff_val] at h_b_minus_7_div
      exact h_b_minus_7_div
    have h_b_minus_7_cases : (b - 7 : ℤ) ∈ ({1, 2, 4, 8} : Finset ℤ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      have h_b_minus_7_dvd : (b - 7 : ℤ) ∣ 8 := h_divisors
      have h_b_minus_7_nonneg : b - 7 ≥ 0 := by linarith [h_b_minus_7_pos]
      have h_b_minus_7_le_8 : b - 7 ≤ 8 := by
        apply Int.le_of_dvd (by norm_num) h_b_minus_7_dvd
      have h_b_minus_7_range : 1 ≤ b - 7 ∧ b - 7 ≤ 8 := by
        constructor
        · linarith [h_b_minus_7_pos]
        · exact h_b_minus_7_le_8
      interval_cases (b - 7 : ℤ)
      · norm_num
      · simp
      · contradiction
      · simp
      · contradiction
      · contradiction
      · contradiction
      · simp
    exact h_b_minus_7_cases
  -- Compute $c - b ∣ f(c) - f(b) = 0 - 85 = -85$.
  have h_c_minus_b_div : (c - b : ℤ) ∣ (f.eval c - f.eval b) := by
    apply Polynomial.sub_dvd_eval_sub
  have h_c_minus_b_vals : (c - b : ℤ) ∈ ({1, 5, 17, 85} : Finset ℤ) := by
    have h_diff : f.eval c - f.eval b = 0 - 85 := by rw [hc, hb]
    have h_diff_val : f.eval c - f.eval b = -85 := by norm_num [h_diff]
    have h_c_minus_b_pos : c - b > 0 := by nlinarith [hord.2]
    have h_divisors : (c - b : ℤ) ∣ -85 := by
      rw [h_diff_val] at h_c_minus_b_div
      exact h_c_minus_b_div
    have h_c_minus_b_dvd : (c - b : ℤ) ∣ 85 := by
      apply Int.dvd_neg.mp
      exact h_divisors
    have h_c_minus_b_nonneg : c - b ≥ 0 := by linarith [h_c_minus_b_pos]
    have h_c_minus_b_le_85 : c - b ≤ 85 := by
      apply Int.le_of_dvd (by norm_num) h_c_minus_b_dvd
    have h_c_minus_b_range : 1 ≤ c - b ∧ c - b ≤ 85 := by
      constructor
      · linarith [h_c_minus_b_pos]
      · exact h_c_minus_b_le_85
    simp only [Finset.mem_insert, Finset.mem_singleton]
    interval_cases (c - b : ℤ) <;> (try norm_num) <;> (try contradiction)
  -- Compute $c - 7 ∣ f(c) - f(7) = 0 - 77 = -77$.
  have h_c_minus_7_div : (c - 7 : ℤ) ∣ (f.eval c - f.eval 7) := by
    apply Polynomial.sub_dvd_eval_sub
  have h_c_minus_7_vals : (c - 7 : ℤ) ∈ ({1, 7, 11, 77} : Finset ℤ) := by
    have h_diff : f.eval c - f.eval 7 = 0 - 77 := by rw [hc, hf]
    have h_diff_val : f.eval c - f.eval 7 = -77 := by norm_num [h_diff]
    have h_c_minus_7_pos : c - 7 > 0 := by nlinarith [hord.1, hord.2]
    have h_divisors : (c - 7 : ℤ) ∣ -77 := by
      rw [h_diff_val] at h_c_minus_7_div
      exact h_c_minus_7_div
    have h_c_minus_7_dvd : (c - 7 : ℤ) ∣ 77 := by
      apply Int.dvd_neg.mp
      exact h_divisors
    have h_c_minus_7_nonneg : c - 7 ≥ 0 := by linarith [h_c_minus_7_pos]
    have h_c_minus_7_le_77 : c - 7 ≤ 77 := by
      apply Int.le_of_dvd (by norm_num) h_c_minus_7_dvd
    have h_c_minus_7_range : 1 ≤ c - 7 ∧ c - 7 ≤ 77 := by
      constructor
      · linarith [h_c_minus_7_pos]
      · exact h_c_minus_7_le_77
    simp only [Finset.mem_insert, Finset.mem_singleton]
    interval_cases (c - 7 : ℤ) <;> (try norm_num) <;> (try contradiction)
  -- Use $(b - 7) + (c - b) = c - 7$ to verify combinations.
  have h_relation : (b - 7) + (c - b) = c - 7 := by ring
  have h_solution : b - 7 = 2 ∧ c - b = 5 ∧ c - 7 = 7 := by
    have h_b_minus_7_cases : b - 7 = 1 ∨ b - 7 = 2 ∨ b - 7 = 4 ∨ b - 7 = 8 := by
      simpa [Finset.mem_insert, Finset.mem_singleton] using h_b_minus_7_vals
    have h_c_minus_b_cases : c - b = 1 ∨ c - b = 5 ∨ c - b = 17 ∨ c - b = 85 := by
      simpa [Finset.mem_insert, Finset.mem_singleton] using h_c_minus_b_vals
    have h_c_minus_7_cases : c - 7 = 1 ∨ c - 7 = 7 ∨ c - 7 = 11 ∨ c - 7 = 77 := by
      simpa [Finset.mem_insert, Finset.mem_singleton] using h_c_minus_7_vals
    have h_check : ∀ x ∈ ({1, 2, 4, 8} : Finset ℤ), ∀ y ∈ ({1, 5, 17, 85} : Finset ℤ),
        x + y ∈ ({1, 7, 11, 77} : Finset ℤ) → x = 2 ∧ y = 5 := by
      intro x hx y hy h_sum
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy h_sum
      rcases hx with h_x_1 | h_x_2 | h_x_4 | h_x_8
      · rw [h_x_1] at h_sum
        rcases hy with h_y_1 | h_y_5 | h_y_17 | h_y_85
        · rw [h_y_1] at h_sum; norm_num at h_sum
        · rw [h_y_5] at h_sum; norm_num at h_sum
        · rw [h_y_17] at h_sum; norm_num at h_sum
        · rw [h_y_85] at h_sum; norm_num at h_sum
      · rw [h_x_2] at h_sum
        rcases hy with h_y_1 | h_y_5 | h_y_17 | h_y_85
        · rw [h_y_1] at h_sum; norm_num at h_sum
        · rw [h_y_5] at h_sum; norm_num at h_sum; exact ⟨h_x_2, h_y_5⟩
        · rw [h_y_17] at h_sum; norm_num at h_sum
        · rw [h_y_85] at h_sum; norm_num at h_sum
      · rw [h_x_4] at h_sum
        rcases hy with h_y_1 | h_y_5 | h_y_17 | h_y_85
        · rw [h_y_1] at h_sum; norm_num at h_sum
        · rw [h_y_5] at h_sum; norm_num at h_sum
        · rw [h_y_17] at h_sum; norm_num at h_sum
        · rw [h_y_85] at h_sum; norm_num at h_sum
      · rw [h_x_8] at h_sum
        rcases hy with h_y_1 | h_y_5 | h_y_17 | h_y_85
        · rw [h_y_1] at h_sum; norm_num at h_sum
        · rw [h_y_5] at h_sum; norm_num at h_sum
        · rw [h_y_17] at h_sum; norm_num at h_sum
        · rw [h_y_85] at h_sum; norm_num at h_sum
    have h_sum_vals : (b - 7) + (c - b) ∈ ({1, 7, 11, 77} : Finset ℤ) := by
      rw [h_relation]
      exact h_c_minus_7_vals
    have h_partial : b - 7 = 2 ∧ c - b = 5 := by
      apply h_check (b - 7) h_b_minus_7_vals (c - b) h_c_minus_b_vals h_sum_vals
    constructor
    · exact h_partial.1
    · constructor
      · exact h_partial.2
      · linarith
  -- Solve for $b$ and $c$ from $b - 7 = 2$, $c - b = 5$, $c - 7 = 7$.
  have h_b : b = 9 := by
    have h_b_minus_7 : b - 7 = 2 := h_solution.1
    linarith
  have h_c : c = 14 := by
    have h_c_minus_b : c - b = 5 := h_solution.2.1
    rw [h_b] at h_c_minus_b
    linarith
  -- Verify $c - 7 = 7$.
  have h_c_minus_7_verify : c - 7 = 7 := by
    rw [h_c]
    norm_num
  -- Combine results.
  have h_result : b = 9 ∧ c = 14 := by
    constructor
    · exact h_b
    · exact h_c
  exact h_result
