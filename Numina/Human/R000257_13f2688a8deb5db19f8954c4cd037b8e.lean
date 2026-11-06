
import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

/- Find all pairs  $(m, n)$  of positive integers for which  $4 (mn +1)$
  is divisible by  $(m + n)^2$ .-/
theorem number_theory_8721 :
  ∀ m n: ℤ, 0 < m ∧ 0 < n ∧ (m + n)^2 ∣ 4 * (m * n + 1) ↔
    (m = 1 ∧ n = 1) ∨ ∃ k : ℕ, 0 < k ∧ (m = k ∧ n = k + 2 ∨ m = k + 2 ∧ n = k ):= by
      intro m n
      constructor <;> intro h
      · -- Because $(m+n)^2 \mid 4mn+4$, we have $(m+n)^2 \leq 4mn+4$.
        have h1 :  (m + n)^2 ≤ 4 * (m * n + 1) := by
          exact Int.le_of_dvd (by simp; refine Int.add_pos_of_nonneg_of_pos (
            Int.mul_nonneg (le_of_lt h.1) (le_of_lt h.2.1)) (by simp)) h.2.2
        simp [add_sq, mul_add] at h1
        rw [add_comm _ 4] at h1
        -- Simplifying the above equation, we have $(m - n) ^ 2 \leq 4$
        have h2 : (m - n) ^ 2 ≤ 4 := by
          simp [sub_sq];  linarith
        -- Assume without loss of generality that \(m \leq n\). 
        wlog hmn : m ≤ n
        · push_neg at hmn
          have := this n m ⟨h.2.1, ⟨h.1, by convert h.2.2 using 1; ring; ring⟩ ⟩
            (by convert h1 using 1; ring; simp [mul_comm]) (by linarith) (le_of_lt hmn)
          rcases this with hl | hr
          · left; tauto
          · obtain ⟨k, hk⟩ := hr
            right; use k; tauto
        · -- $(m - n) ^ 2 = (n - m) ^ 2 $.
          replace h2 : (n - m) ^ 2 ≤ 4 := by linarith
          by_cases meqn : m = n
          · -- when $m = n$, replace $m$ with $n$ in `h`, we can get $m = n = 1$.
            simp [meqn, ←Int.two_mul, mul_pow,←pow_two, mul_add] at h
            have := Int.le_of_dvd (by linarith) h.2
            have : n = 1 := by
              have : n ^ 2 ≤ 1 := by linarith
              have := (sq_le_one_iff (le_of_lt h.1)).1 this
              omega
            left; omega
          · -- When $m < n$, $n - m ≤ 2 $ because of $(n - m) ^ 2 ≤ 4$.
            replace meqn : m < n := by omega
            have h3 : n - m ≤ 2 := by
              rw [show (4 : ℤ) = 2 ^ 2 by linarith] at h2
              exact (pow_le_pow_iff_left (by linarith) (by simp) (by simp)).1 h2
            have : 0 < n - m := by omega
            set k := n - m with hk
            -- discuss the value of $n - m$.
            interval_cases k
            · -- $n - m = 1$ is impossible.
              replace : n = m + 1 := by omega
              simp [this] at h
              have := h.2.2; ring_nf at this
              rw [show 4 + m * 4 + m ^ 2 * 4 = 1 + m * 4 + m ^ 2 * 4 + 3 by linarith] at this
              have h4 := Int.dvd_sub this (Int.dvd_refl _)
              simp at h4
              have := Int.le_of_dvd (by positivity) h4
              have : m ≤ 0 := by
                by_contra! tmp
                replace tmp : 1 ≤ m := Int.add_one_le_of_lt tmp
                have h5 : 1 + 1 * 4 + 1 ^ 2 * 4 ≤ 1 + m * 4 + m ^ 2 * 4 :=
                  Int.add_le_add (by linarith) (Int.mul_le_mul_of_nonneg_right (pow_le_pow_left h3 tmp 2) (by simp))
                simp at h5; linarith
              exfalso; linarith
            · -- $n - m = 2$ always satisfy the condition.
              replace hk : n = m + 2:= by omega
              right; use m.natAbs
              rw [←Int.eq_natAbs_of_zero_le (le_of_lt h.1)]
              exact ⟨by simp; linarith, by left; tauto⟩
      · -- Check the sufficiency.
        rcases h with h1 | ⟨k, hk, h2 | h3⟩
        · simp [h1]; decide
        · simp [h2]; norm_cast; exact ⟨hk, by linarith, by ring_nf; rfl⟩
        · simp [h3]; norm_cast; exact ⟨by linarith, hk, by ring_nf; rfl⟩
