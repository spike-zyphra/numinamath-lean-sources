import Mathlib

theorem algebra_161509 {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hsum : p + q = 1) (h : (Nat.choose 9 1) * (p ^ 8 * q ^ 1) = (Nat.choose 9 2) * (p ^ 7 * q ^ 2)) :
    p = 4 / 5 := by
  have h1 : (Nat.choose 9 1 : ℝ) = 9 := by
    norm_num [Nat.choose]
  have h2 : (Nat.choose 9 2 : ℝ) = 36 := by
    norm_num [Nat.choose]
  rw [h1, h2] at h
  have eq1 : (9 : ℝ) * (p ^ 8 * q ^ 1) = (36 : ℝ) * (p ^ 7 * q ^ 2) := by 
    linarith
  -- Simplify the equation to get $p \cdot q = 4 \cdot q^2$.
  have h3 : p * q = 4 * q ^ 2 := by
    have h8 : p ^ 8 * q ^ 1 = 4 * (p ^ 7 * q ^ 2) := by
      nlinarith
    -- Simplify h8 to get $p \cdot q = 4 \cdot q^2$.
    have h9 : p * q = 4 * q ^ 2 := by
      nlinarith [h8, pow_pos hp 7, pow_pos hq 2, pow_pos hq 1, pow_pos hp 1]
    linarith
  -- From $p \cdot q = 4 \cdot q^2$ and $q > 0$, we get $p - 4 \cdot q = 0$.
  have h4 : p - 4 * q = 0 := by
    apply (mul_right_inj' (ne_of_gt hq)).mp
    linarith
  -- From $p - 4q = 0$, we get $p = 4q$.
  have h5 : p = 4 * q := by
    linarith
  -- Using $p + q = 1$, we solve for $q$.
  have h6 : q = 1 / 5 := by
    have eq2 : p + q = 1 := hsum
    rw [h5] at eq2
    linarith
  -- Substituting $q = 1/5$ into $p = 4q$, we get $p = 4/5$.
  have h7 : p = 4 / 5 := by 
    rw [h5]
    rw [h6]
    norm_num
  exact h7