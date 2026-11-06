import Mathlib

def is_perfect (n : ℕ) := ∑ d in n.divisors.erase n, d = n

theorem number_theory_69752 {f : ℕ → ℤ} (hf1 : ∀ n, is_perfect n → f n = 0)
    (hf2 : ∀ n, n % 10 = 4 → f n = 0) (hf3 : ∀ a b, f (a * b) = f a + f b) :
    f 1998 = 0 := by
  have h1 : f 1998 = f 6 + f 333 := by
    calc
      f 1998 = f (6 * 333) := by norm_num
      _ = f 6 + f 333 := by rw [hf3 6 333]
  have h2 : f 6 = 0 := by
    have h3 : is_perfect 6 := by
      unfold is_perfect
      native_decide
    have h4 : f 6 = 0 := hf1 6 h3
    exact h4
  have h5 : f 333 = f 3 + f 111 := by
    calc
      f 333 = f (3 * 111) := by norm_num
      _ = f 3 + f 111 := by rw [hf3 3 111]
  have h6 : f 111 = f 3 + f 37 := by
    calc
      f 111 = f (3 * 37) := by norm_num
      _ = f 3 + f 37 := by rw [hf3 3 37]
  have h7 : f 2 = 0 := by
    have h8 : f 4 = 0 := by
      apply hf2 4
      all_goals norm_num
    have h9 : f 4 = f 2 + f 2 := by
      calc
        f 4 = f (2 * 2) := by norm_num
        _ = f 2 + f 2 := by rw [hf3 2 2]
    linarith [h8, h9]
  have h8 : f 3 = 0 := by
    have h9 : f 6 = 0 := h2
    have h10 : f 6 = f 2 + f 3 := by
      calc
        f 6 = f (2 * 3) := by norm_num
        _ = f 2 + f 3 := by rw [hf3 2 3]
    linarith [h7, h10, h9]
  have h11 : f 37 = 0 := by
    have h12 : f 74 = 0 := by
      apply hf2 74
      all_goals norm_num
    have h13 : f 74 = f 2 + f 37 := by
      calc
        f 74 = f (2 * 37) := by norm_num
        _ = f 2 + f 37 := by rw [hf3 2 37]
    linarith [h7, h12, h13]
  have h14 : f 333 = 0 := by
    linarith [h5, h6, h8, h11]
  linarith [h1, h2, h14]