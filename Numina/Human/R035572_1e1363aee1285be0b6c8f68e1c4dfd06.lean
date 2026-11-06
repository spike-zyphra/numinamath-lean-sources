import Mathlib

/- Problem 5. Solve the system of equations

$$
\left\{\begin{array}{l}
5 x^{2}+14 x y+10 y^{2}=17 \\
4 x^{2}+10 x y+6 y^{2}=8
\end{array}\right.
$$ -/
theorem algebra_241074 (x y : ℝ) :
    (5 * x ^ 2 + 14 * x * y + 10 * y ^ 2 = 17 ∧ 4 * x ^ 2 + 10 * x * y + 6 * y ^ 2 = 8) ↔
    (x = -1 ∧ y = 2) ∨ (x = 11 ∧ y = -7) ∨ (x = -11 ∧ y = 7) ∨ (x = 1 ∧ y = -2) := by
  constructor
  -- forward
  · intro ⟨h1, h2⟩
    have eq_aux1 : (3 * x + 4 * y) ^ 2 = 25 := by nlinarith
    have eq_aux2 : (x + 2 * y) ^ 2 = 9 := by nlinarith
    -- now leads to four cases 
    have eq_aux3 : 3 * x + 4 * y = 5 ∨ 3 * x + 4 * y = -5 := by apply eq_or_eq_neg_of_sq_eq_sq <;> linarith
    obtain h3 | h3 := eq_aux3
    have eq_aux4 :  x + 2 * y = 3 ∨  x + 2 * y = -3 := by apply eq_or_eq_neg_of_sq_eq_sq <;> linarith
    obtain h4 | h4 := eq_aux4
    -- check each case
    left
    constructor
    nlinarith
    nlinarith
    right; left
    constructor
    · calc 
        _ = (3 * x + 4 * y) - 2 * (x + 2 * y) := by ring
        _ = 11 := by rw [h3, h4]; norm_num
    nlinarith
    have eq_aux4 :  x + 2 * y = 3 ∨  x + 2 * y = -3 := by apply eq_or_eq_neg_of_sq_eq_sq <;> linarith
    obtain h4 | h4 := eq_aux4
    right; right; left
    constructor
    nlinarith; nlinarith
    right; right; right
    constructor
    nlinarith; nlinarith
  -- backward
  · intro h
    obtain h | h | h | h := h
    all_goals simp [h]; ring_nf; norm_num
  