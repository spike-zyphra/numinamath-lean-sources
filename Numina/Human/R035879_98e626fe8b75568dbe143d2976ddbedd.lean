import Mathlib

/- Find all ordered pairs $(a, b)$ of positive integers for which the numbers $\frac{a^{3} b-1}{a+1}$ and $\frac{b^{3} a+1}{b-1}$ are positive integers. -/
theorem number_theory_605558 :
  {(a, b) : ℤ × ℤ | 0 < a ∧ a ≤ b ∧ 1 < b ∧ 0 < a^3*b - 1 ∧ a + 1 ∣ (a^3*b - 1) ∧ b - 1 ∣ b^3*a + 1} 
  = {(1,3), (2,2), (3,3)} := by 
    ext ⟨x, y⟩ 
    simp 
    constructor 
    · intro ⟨xpos, xley, ygt1, numpos, h1, h2⟩
      -- $a^{3} b-1=b\left(a^{3}+1\right)-(b+1)$ 
      have c1 : x^3*y - 1 = y*(x^3+1) - (y+1) := by ring
      -- $b^{3} a+1=a\left(b^{3}-1\right)+(a+1)$ 
      have c2 : y^3*x + 1 = x*(y^3-1) + (x + 1) := by ring
      rw [c1] at h1
      rw [c2] at h2 
      -- $a+1 \mid a^{3}+1$
      have dvd1 : x + 1 ∣ x^3 + 1 := by 
        suffices x^3 + 1 = (x+1) * (x^2 - x + 1) by simp [this]
        linarith
      --  $b-1 \mid b^{3}-1$
      have dvd2 : y - 1 ∣ y^3 - 1 := by 
        suffices y^3 - 1 = (y-1) * (y^2+y+1) by simp [this]
        linarith 
      -- -- As $b^{3} a+1=a\left(b^{3}-1\right)+(a+1)$ and $b-1 \mid b^{3}-1$, we have $b-1 \mid a+1$.
      have h3 : y - 1 ∣ x + 1 := 
        (Int.dvd_add_right (Dvd.dvd.mul_left dvd2 x)).1 h2
      -- As $a^{3} b-1=b\left(a^{3}+1\right)-(b+1)$ and $a+1 \mid a^{3}+1$, we have $a+1 \mid b+1$.
      have h4 : x + 1 ∣ y + 1 := 
        (dvd_sub_right (Dvd.dvd.mul_left dvd1 y)).1 h1
      -- So $b-1 \mid b+1$ and hence $b-1 \mid 2$.
      have h5 : y - 1 ∣ y + 1 := h3.trans h4 
      replace h5 : y - 1 ∣ 2 := by 
        rw [show 2 = y + 1 - (y - 1) by norm_num]
        apply Int.dvd_sub h5 
        rfl
      replace h5 := Int.le_of_dvd (by positivity) h5
      simp at h5
      -- We have $1 ≤ y ≤ 3$, so y can only be 2 or 3.
      interval_cases y <;> interval_cases x <;> simp at h4 <;> tauto
    · intro h
      rcases h with h | h | h  <;> norm_num [h] 