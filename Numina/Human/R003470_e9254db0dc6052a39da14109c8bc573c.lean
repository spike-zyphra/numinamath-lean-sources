import Mathlib

-- Show that if a ≠ 0 and a^2 * b is a square, then b is also a square.
theorem lemma_1 {a b k : ℕ} (ha : a ≠ 0) (hk : a^2 * b = k^2) : ∃ m, b = m^2 := by
  -- a² divides k² implies that a divides k
  have h₁ : a ∣ k := by
    have h : a^2 ∣ k^2 := by use b; rw [hk]
    rwa [Nat.pow_dvd_pow_iff (by norm_num)] at h
  -- We get k = a * t
  rcases h₁ with ⟨t, rfl⟩
  -- Show that b = t^2.
  use t
  rw [← mul_right_inj' (show a^2 ≠ 0 by positivity)]
  linear_combination hk

/- 2 - 87 Let $4^{27}+4^{500}+4^{n}$ be a square number (the square of an integer), find the maximum value of the integer $n$.
 -/
theorem number_theory_185918 :
    IsGreatest {n | ∃ k, (4^27 + 4^500 + 4^n) = k^2} 972 := by
  simp only [IsGreatest, Set.mem_setOf_eq, upperBounds, forall_exists_index]
  constructor
  -- Show that 4^27 + 4^500 + 4^972 is a square.
  · use 2^27 * (2^(972 - 27) + 1)
    norm_num
  intro n k h
  -- Assume that 4^27 + 4^500 + 4^n is a square. Show that n ≤ 972.
  -- Assume that 972 < n and show that 4^27 + 4^500 + 4^n is not a square.
  contrapose! h
  -- We have 4^27 + 4^500 + 4^n = (2^27)^2 * ((2^(n - 27))^2 + 2 * 2^945 + 1).
  have eq : 4^27 + 4^500 + 4^n = (2^27)^2 * ((2^(n - 27))^2 + 2 * 2^945 + 1) := calc
    _ = 4^27 * (4^(n - 27) + 4^473 + 1) := by
      simp_rw [mul_add, ← pow_add, show 27 + (n - 27) = n by omega]
      ring
    _ = (2^27)^2 * ((2^(n - 27))^2 + 2 * 2^945 + 1) := by
      rw [show 4^473 = 2 * 2^945 by norm_num]
      rw [show 4^27 = (2^27)^2 by norm_num]
      suffices 4^(n - 27) = (2^(n - 27))^2 by rw [this]
      rw [show 4 = 2 ^ 2 by norm_num]
      simp_rw [← pow_mul]
      ring_nf
  rw [eq]; clear eq
  -- Let a = 2^27, b = 2^945, c = 2^(n - 27).
  -- We need to show that a^2 * (c^2 + 2 * b + 1) is not a square.
  generalize ha : 2^27 = a
  generalize hb : 2^945 = b
  generalize hc : 2^(n - 27) = c
  intro h1
  -- lemma_1 implies that it is enough to show that c^2 + 2 * b + 1 is not a square.
  have ⟨m, hm⟩ := lemma_1 (show a ≠ 0 by positivity) h1
  contrapose! hm
  clear h1 hm
  -- Consider two cases: m ≤ c and c < m.
  by_cases hm : m ≤ c
  · -- Assume that m ≤ c and show that m^2 < c^2 + 2 * b + 1.
    apply ne_of_gt
    calc
      m^2 ≤ c^2 + 0 + 0 := by
        rwa [add_zero, add_zero, sq_le_sq₀ (by simp) (by simp)]
      _ < c^2 + 2 * b + 1 := by
        gcongr
        · positivity
        · norm_num
  · -- Assume that c < m and show that c^2 + 2 * b + 1 < m^2.
    -- We have c + 1 ≤ m so (c + 1)^2 = c^2 + 2 * c + 1 ≤ m^2.
    -- On the other hand, c^2 + 2 * c + 1 > c^2 + 2 * b + 1 because c > b.
    rw [not_le, ← Nat.add_one_le_iff] at hm
    apply ne_of_lt
    calc
      c^2 + 2 * b + 1 < c^2 + 2 * c + 1 := by
        gcongr
        rw [← hb, ← hc]
        apply pow_lt_pow_right₀ one_lt_two (by omega)
      _ = (c + 1)^2 := by ring
      _ ≤ m^2 := by nlinarith