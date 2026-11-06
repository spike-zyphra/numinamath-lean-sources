import Mathlib

/- Let $a,b,c$ three positive numbers less than $ 1$. Prove that cannot occur simultaneously these three inequalities:
$$a (1- b)>\frac14$$
$$b (1-c)>\frac14 $$ 
$$c (1-a)>\frac14$$ -/
theorem inequalities_57095 (a b c : ℝ) (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1) (hc : 0 < c ∧ c < 1)
    (h1 : a * (1 - b) > 1 / 4) (h2 : b * (1 - c) > 1 / 4) (h3 : c * (1 - a) > 1 / 4) :
    False := by
  nlinarith [mul_self_nonneg (a - 1 / 2), mul_self_nonneg (b - 1 / 2), mul_self_nonneg (c - 1 / 2)]