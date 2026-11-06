import Mathlib

/- Laat $m$ en $n$ positieve gehele getallen zijn zodat $5 m+n$ een deler is van $5 n+m$. Bewijs dat $m$ een deler is van $n$. -/
theorem number_theory_605469 (m n : ℤ) (hm : 0 < m) (hn : 0 < n)
    (h : 5 * m + n ∣ 5 * n + m) : m ∣ n := by 
    -- There is a positive integer $k$ with $(5 m+n) k=5 n+m$.
  have h_k_exists : ∃ k : ℤ, k > 0 ∧ (5 * m + n) * k = 5 * n + m := by
    obtain ⟨k, hk⟩ := h
    have h_divisor_pos : 5 * m + n > 0 := by linarith [hm, hn]
    have h_dividend_pos : 5 * n + m > 0 := by linarith [hm, hn]
    have h_k_pos : k > 0 := by
      by_contra h_contra
      push_neg at h_contra
      have : (5 * m + n) * k ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) h_contra
      rw [← hk] at this
      linarith
    exact ⟨k, h_k_pos,Eq.symm hk⟩

  -- So $5 k m-m=5 n-k n$, or $(5 k-1) m=(5-k) n$.
  obtain ⟨k, hk_pos, hk_eq⟩ := h_k_exists
  have h_eq_rewrite : (5 * k - 1) * m = (5 - k) * n := by
    apply eq_of_sub_eq_zero
    have : (5 * m + n) * k = 5 * n + m := hk_eq
    calc
      (5 * k - 1) * m - (5 - k) * n
      = 5 * k * m - m - (5 * n - k * n) := by ring
      _ = 5 * k * m - m - 5 * n + k * n := by ring
      _ = (5 * k * m + k * n) - (5 * n + m) := by ring
      _ = k * (5 * m + n) - (5 * n + m) := by ring
      _ = (5 * m + n) * k - (5 * n + m) := by rw [mul_comm]
      _ = 0 := by rw [this];ring

  -- The left side is positive, so the right side is also positive, which implies that $k&lt;5$.
  have h_k_bound : k < 5 := by
    have h_left_pos : (5 * k - 1) * m > 0 := by
      have : m > 0 := hm
      suffices t : 5 * k - 1 > 0 by nlinarith
      have : k ≥ 1 := by linarith [hk_pos]
      have : 5 * k ≥ 5 := by linarith
      linarith
    have : 5 * n + m > 0 := by linarith [hm, hn]
    have : (5 * n + m) * k > 0 := by nlinarith
    have : (5 * k - 1) * m = (5 - k) * n := h_eq_rewrite
    have : (5 - k) * n > 0 := by
      rw [← this]
      exact h_left_pos
    nlinarith

  -- Case analysis for $k = 1, 2, 3, 4$.
  have h_cases : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by
    have : k ≥ 1 := by linarith [hk_pos]
    interval_cases k
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))


  -- If $k=1$, then $4 m=4 n$, so $m=n$, thus $m|n$. If $k=2$, then $9 m=3 n$, so $3 m=n$, thus $m|n$. If $k=3$, then $14 m=2 n$, so $7 m=n$, thus $m|n$. If $k=4$, then $19 m=n$, thus $m|n$.
  have h_m_div_n : m ∣ n := by
    cases h_cases with
    | inl h_k1 =>
      rw [h_k1] at h_eq_rewrite
      have : 4 * m = 4 * n := by linarith [h_eq_rewrite]
      have : m = n := by linarith
      use 1
      rw [this]
      linarith
    | inr h_k_rest =>
      cases h_k_rest with
      | inl h_k2 =>
        rw [h_k2] at h_eq_rewrite
        have : 9 * m = 3 * n := by linarith [h_eq_rewrite]
        have : n = 3 * m := by linarith
        use 3
        rw [this]
        linarith
      | inr h_k_rest2 =>
        cases h_k_rest2 with
        | inl h_k3 =>
          rw [h_k3] at h_eq_rewrite
          have : 14 * m = 2 * n := by linarith [h_eq_rewrite]
          have : n = 7 * m := by linarith
          use 7
          rw [this]
          linarith
        | inr h_k4 =>
          rw [h_k4] at h_eq_rewrite
          have : 19 * m = n := by linarith [h_eq_rewrite]
          use 19
          linarith
  exact h_m_div_n
