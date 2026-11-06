import Mathlib
set_option maxHeartbeats 500000
/- ## Task B-1.5.

Determine all integer solutions of the equation


$$

(m n-3)^{2}=m^{2}+n^{2}-4 m n

$$
 -/
theorem algebra_233802 (m n : ℤ) :
    (m * n - 3)^2 = m^2 + n^2 - 4 * m * n → (m = 1 ∧ n = 4) ∨ (m = 4 ∧ n = 1) ∨ (m = -1 ∧ n = -4) ∨ (m = -4 ∧ n = -1) ∨
    (m = 0 ∧ n = -3) ∨ (m = 0 ∧ n = 3) ∨ (m = 3 ∧ n = 0) ∨ (m = -3 ∧ n = 0) := by
      intro H
      --Obtain the following factorization of H.
      have H0 : (m + n - m * n) * (m + n + m * n) = 9 := by linarith
      --Now it follows that (m + n - m * n) and (m + n + m * n) are divisors of 9. We get six cases.
      have cases : ((m + n - m * n) = 1 ∧ (m + n + m * n) = 9) ∨ ((m + n - m * n) = -1 ∧ (m + n + m * n) = -9)
        ∨ ((m + n - m * n) = 9 ∧ (m + n + m * n) = 1) ∨ ((m + n - m * n) = -9 ∧ (m + n + m * n) = -1)
        ∨ ((m + n - m * n) = 3 ∧ (m + n + m * n) = 3) ∨ ((m + n - m * n) = -3 ∧ (m + n + m * n) = -3) := by
          have cases' : (m + n - m * n) = 1 ∨ (m + n - m * n) = -1 ∨ (m + n - m * n) = 9 ∨ (m + n - m * n) = -9
            ∨ (m + n - m * n) = 3 ∨ (m + n - m * n) = -3 := by
              --We find the divisors of 9 and use them to show `cases`.
              have h : (m + n - m * n) ∣ 9 := by
                use (m + n + m * n)
                exact id (Eq.symm H0)
              have ha : (m + n - m * n).natAbs ∈ (9).divisors := by
                have ⟨b, hb⟩ := h
                simp; use b.natAbs; rw [←Int.natAbs_mul, ← hb]; rfl
              simp [show (9 : ℕ).divisors = {1,3,9} from rfl] at ha
              omega

          rcases cases' with h1|h2|h3|h4|h5|h6
          --case 1:
          left
          have : (m + n + m * n) = 9 := by
            rw [h1] at H0
            omega
          exact ⟨h1, this⟩
          --case 2:
          right; left
          have : (m + n + m * n) = -9 := by
            rw [h2] at H0
            omega
          exact ⟨h2, this⟩
          --case 3:
          right; right; left
          have : (m + n + m * n) = 1 := by
            rw [h3] at H0
            omega
          exact ⟨h3, this⟩
          --case 4:
          right; right; right; left
          have : (m + n + m * n) = -1 := by
            rw [h4] at H0
            omega
          exact ⟨h4, this⟩
          --case 5:
          right; right; right; right; left
          have : (m + n + m * n) = 3 := by
            rw [h5] at H0
            omega
          exact ⟨h5, this⟩
          --case 6:
          right; right; right; right; right
          have : (m + n + m * n) = -3 := by
            rw [h6] at H0
            omega
          exact ⟨h6, this⟩
      --We now show that the second and third cases are impossible.
      have not_case_2 : ¬ (((m + n - m * n) = -1 ∧ (m + n + m * n) = -9)) := by
        by_contra h
        have h1 : (m + n - m * n) = -1 := h.1
        have h2 : (m + n + m * n) = -9 := h.2
        have h3 : m + n = -5 := by
          linarith
        have h5 : m * n = - 4 := by
          linarith
        --Now using `h5` we look at the possible values of m and n.
        have cases_2' : m = -1 ∨ m = 1 ∨ m = -2 ∨ m = 2 := by
              have h6 : m + n = -5 := h3
              have h7 : m * n = -4 := h5
              -- Now we need to solve for integers m and n where m + n = -5 and m * n = -4
              -- Let's substitute n = -5 - m into m * n = -4
              -- m * (-5 - m) = -4
              -- -5m - m^2 = -4
              -- m^2 + 5m - 4 = 0
              -- The discriminant is 25 + 16 = 41, which is not a perfect square
              -- Therefore, there are no integer solutions
              -- Lean's proof should detect this contradiction
              have h8 : m ≤ 4 := by
                nlinarith [sq_nonneg (m + 2), sq_nonneg (n + 2), h6, h7]
              have h9 : m ≥ -9 := by
                nlinarith [sq_nonneg (m + 2), sq_nonneg (n + 2), h6, h7]
              interval_cases m <;> omega
        --Now we find n in each case and show that m and n don't satisfy m + n = -5.
        rcases cases_2' with c|c|c|c
        all_goals
        rw [c] at h3
        rw [c] at h5
        omega
      have not_case_3 : ¬ ((m + n - m * n) = 9 ∧ (m + n + m * n) = 1) := by
        by_contra h
        have h1 : (m + n - m * n) = 9 := h.1
        have h2 : (m + n + m * n) = 1 := h.2
        have h3 : m + n = 5 := by
          linarith
        have h5 : m * n = -4 := by
          linarith
        --Now using `h5` we look at the possible values of m and n.
        have cases_2' : m = -1 ∨ m = 1 ∨ m = -2 ∨ m = 2 := by
              have h4 : m + n = 5 := h3
              have h6 : m * n = -4 := h5
              have h9 : n = 5 - m := by
                linarith
              rw [h9] at h6
              -- Now we have $m(5 - m) = -4$ which expands to $5m - m^2 = -4$
              -- Rearranging gives $m^2 - 5m - 4 = 0$
              -- Let's check that this quadratic has no integer solutions
              -- $m^2 - 5m - 4 = 0$ implies $m = \frac{5 \pm \sqrt{41}}{2}$ which is not integer
              have h10 : m^2 - 5 * m - 4 = 0 := by
                nlinarith
              -- Show that $m^2 - 5m - 4 \neq 0$ for all integers $m$
              have h11 : m^2 - 5 * m - 4 ≠ 0 := by
                -- We can check all possible integer values for m
                -- $m^2 - 5m - 4 = 0$ implies $m \in [0, 5]$ approximately
                -- Check integer values in this range
                have h3 : m ≤ 5 := by nlinarith [sq_nonneg (m - 5)]
                have h4 : m ≥ -1 := by nlinarith [sq_nonneg (m - 5)]
                interval_cases m <;> omega
              -- Contradiction arises because we have $m^2 - 5m - 4 = 0$ and $m^2 - 5 m - 4 \neq 0$
              contradiction
        rcases cases_2' with c|c|c|c
        all_goals
        rw [c] at h3
        rw [c] at h5
        omega
      --So We get rid of the second and third cases.
      have cases' : ((m + n - m * n) = 1 ∧ (m + n + m * n) = 9) ∨ ((m + n - m * n) = -9 ∧ (m + n + m * n) = -1)
        ∨ ((m + n - m * n) = 3 ∧ (m + n + m * n) = 3) ∨ ((m + n - m * n) = -3 ∧ (m + n + m * n) = -3) := by tauto
      rcases cases' with (h1 | h2 | h3 | h4)
      · -- First case: m + n - m * n = 1 and m + n + m * n = 9
        have h5 : m + n = 5 := by
          linarith
        have h6 : m * n = 4 := by
          nlinarith
        have h7 : m = 1 ∨ m = 4 := by
          have h8 : m * n = 4 := h6
          have h9 : m + n = 5 := h5
          have h10 : m ≤ 5 := by nlinarith
          have h11 : m ≥ -5 := by nlinarith
          interval_cases m <;> omega
        cases h7 with
        | inl hm1 =>
          have hn1 : n = 4 := by linarith
          left
          exact ⟨hm1, hn1⟩
        | inr hm2 =>
          have hn2 : n = 1 := by linarith
          right
          left
          exact ⟨hm2, hn2⟩
      · -- Second case: m + n - m * n = -9 and m + n + m * n = -1
        have h5 : m + n = -5 := by
          linarith
        have h6 : m * n = 4 := by
          nlinarith
        have h7 : m = -1 ∨ m = -4 := by
          have h8 : m * n = 4 := h6
          have h9 : m + n = -5 := h5
          have h10 : m ≤ 0 := by nlinarith
          have h11 : m ≥ -5 := by nlinarith
          interval_cases m <;> omega
        cases h7 with
        | inl hm1 =>
          have hn1 : n = -4 := by linarith
          right
          right
          left
          exact ⟨hm1, hn1⟩
        | inr hm2 =>
          have hn2 : n = -1 := by linarith
          right
          right
          right
          left
          exact ⟨hm2, hn2⟩
      · -- Third case: m + n - m * n = 3 and m + n + m * n = 3
        have h5 : m + n = 3 := by
          linarith
        have h6 : m * n = 0 := by
          nlinarith
        cases (mul_eq_zero.mp h6) with
        | inl hm1 =>
          have hn1 : n = 3 := by linarith
          right
          right
          right
          right
          right
          left
          exact ⟨by omega, hn1⟩
        | inr hn1 =>
          have hm1 : m = 3 := by linarith
          right
          right
          right
          right
          right
          right
          left
          exact ⟨hm1, by omega⟩
      · -- Fourth case: m + n - m * n = -3 and m + n + m * n = -3
        have h5 : m + n = -3 := by
          linarith
        have h6 : m * n = 0 := by
          nlinarith
        cases (mul_eq_zero.mp h6) with
        | inl hm1 =>
          have hn1 : n = -3 := by linarith
          right
          right
          right
          right
          left
          exact ⟨by omega, hn1⟩
        | inr hn1 =>
          have hm1 : m = -3 := by linarith
          right
          right
          right
          right
          right
          right
          right
          exact ⟨hm1, by omega⟩