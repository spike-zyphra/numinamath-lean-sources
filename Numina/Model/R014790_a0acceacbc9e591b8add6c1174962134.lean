import Mathlib

theorem algebra_321582 {a b : ℕ → ℝ} (ha : ∃ d, ∀ n, a n = a 0 + d * n)
    (hb : ∃ r, ∀ n, b n = b 0 * r ^ n) (h1 : a 0 = b 0) (h2 : 0 < a 0) (h3 : 0 < b 0)
    (h4 : a 1 = b 1) (h5 : 0 < a 1) (h6 : 0 < b 1) :
    ∀ n, a n ≤ b n := by
  rcases ha with ⟨d, had⟩
  rcases hb with ⟨r, hbl⟩
  have h7 : a 1 = a 0 + d := by
    specialize had 1
    ring_nf at had ⊢
    linarith
  have h8 : b 1 = b 0 * r ^ 1 := by
    specialize hbl 1
    simpa using hbl
  have h_eq1 : d = a 0 * (r - 1) := by
    rw [h7] at h4
    rw [h1, h8] at h4
    nlinarith
  intro n
  have h7n : a n = a 0 + a 0 * (r - 1) * (n : ℝ) := by
    rw [had n]
    rw [h_eq1]
    <;> ring_nf <;> linarith
  have h8n : b n = b 0 * r ^ n := by
    apply hbl
  rw [h7n, h8n]
  have h7r : r > 0 := by
    have hr1 : b 1 > 0 := h6
    rw [hbl 1] at hr1
    nlinarith [h1, h2, h3, h5, h6]
  have h9' : 1 + (r - 1) * (n : ℝ) ≤ r ^ (n : ℕ) := by
    have h10' : ∀ n : ℕ, 1 + (r - 1) * (n : ℝ) ≤ r ^ (n : ℕ) := by
      intro n
      induction n with
      | zero =>
        norm_num
      | succ n ih =>
        have h9 : (r : ℝ) ^ (n + 1 : ℕ) = (r ^ (n : ℕ)) * r := by
          simp [pow_add]
          <;> ring_nf <;> simp [pow_add] <;> ring_nf
        have h10 : (1 : ℝ) + (r - 1) * ((n + 1 : ℕ) : ℝ) = (1 : ℝ) + (r - 1) * (n : ℝ) + (r - 1) := by
          simp [Nat.cast_add, mul_add]
          <;> ring_nf <;> simp [Nat.cast_add, mul_add] <;> ring_nf
        rw [h9, h10]
        nlinarith [pow_pos (show r > 0 by linarith) (n + 1), sq_nonneg (r - 1), sq_nonneg r, sq_nonneg (r ^ (n : ℕ) - 1), mul_pos (show r > 0 by linarith) (show r > 0 by linarith)]
    specialize h10' n
    exact_mod_cast h10'  -- Convert the goal to goals without this function
  have h10 : a 0 > 0 := by linarith
  have h11 : a 0 = b 0 := by linarith
  have h5r : r ^ (n : ℕ) > 0 := by positivity
  nlinarith [h7r, h9', h10, h5r, h11, h6]