import Mathlib

theorem number_theory_109973 (x y : ℕ) (hx : x < 10) (hy : y < 10)
    (h : ∃ n, n^2 = 10000 * x + 1000 * y + 111) :
    x = 0 ∧ y = 9 := by
  rcases h with ⟨n, hn⟩
  have h1 : n ≤ 332 := by
    -- bound n by sqrt(10000 * 9 + 1000 * 9 + 111)
    nlinarith [sq_nonneg (n : ℕ), hx, hy, show 10000 * x + 1000 * y + 111 < 100000 by 
      omega 
    ]
  interval_cases n <;> omega