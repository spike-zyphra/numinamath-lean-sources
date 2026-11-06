import Mathlib

theorem algebra_233636 {n : ℕ} (h₀ : n < 100) (h₁ : n > 9)
    (h₂ : (n / 10) = (n % 10) + 3) (h₃ : n % (n / 10 + n % 10) = 3) :
    n / 10 + n % 10 = 7 := by
  interval_cases n <;> norm_num at h₂ h₃ ⊢ <;> all_goals
    try { trivial }
    <;> try { omega }
    <;> try { try { contradiction } <;> try { simp } }
    <;> try { try { linarith } <;> try { omega } }