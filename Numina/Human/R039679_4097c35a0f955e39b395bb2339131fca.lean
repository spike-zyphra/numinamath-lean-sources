import Mathlib

/- (a) Laat $a$ en $b$ positieve gehele getallen zijn zodat $M(a, b)=a-\frac{1}{b}+b\left(b+\frac{3}{a}\right)$ een geheel getal is. Bewijs dat $M(a, b)$ een kwadraat is.-/
theorem number_theory_604351_1 {a b : ℤ} (ha : 0 < a) (hb : 0 < b)
    (h : ∃ k : ℤ, (a - 1 / b + b * (b + 3 / a) : ℚ) = k) :
    ∃ z : ℤ, z ^ 2 = (a - 1 / b + b * (b + 3 / a) : ℚ) := by

    -- Let k' be the integer a - 1 / b + b * (b + 3 / a)
    obtain ⟨k', hk'⟩ := h

    -- reformulate the formula, we get M(a, b) = (a + b ^ 2) + (3 * b ^ 2 - a) / (a * b)
    have : (a - 1 / b + b * (b + 3 / a) : ℚ) = (a + b ^ 2) + (3 * b ^ 2 - a) / (a * b) := by
      field_simp; ring
    rw [this] at hk'

    -- Since $a+b^{2}$ is an integer, $-\frac{1}{b}+\frac{3 b}{a}$ is also an integer. This can be written as $\frac{-a+3 b^{2}}{a b}$.
    have : ∃ k : ℤ, k = ((3 * b ^ 2 - a) / (a * b) : ℚ) := by
      use k' - a - b ^ 2
      field_simp at hk' ⊢
      linarith

    -- We see that $a b$ is a divisor of $3 b^{2}-a$.
    have h1 : a * b ∣ 3 * b ^ 2 - a := by
      obtain ⟨d, hd⟩ := this
      field_simp at hd
      norm_cast at hd
      exact Dvd.intro_left d hd

    -- In particular, $b$ is a divisor of $3 b^{2}-a$
    have h2 : b ∣ 3 * b ^ 2 - a := by exact dvd_of_mul_left_dvd h1

    -- and thus $b \mid a$.
    have h2 : b ∣ a := by
      suffices h : b ∣ -a by exact Int.dvd_neg.mp h
      rw [show -a = 3 * b ^ 2 - a - 3 * b ^ 2 by ring]
      refine Int.dvd_sub h2 ?_
      rw [pow_two, ← mul_assoc]
      exact Int.dvd_mul_left (3 * b) b

    -- But that means $b^{2}$ is a divisor of $a b$
    have h3 : b ^ 2 ∣ a * b := by
      rw [pow_two]
      exact Int.mul_dvd_mul_right b h2

    -- and therefore also of $3 b^{2}-a$
    have h4 : b ^ 2 ∣ 3 * b ^ 2 - a := by
      exact Int.dvd_trans h3 h1

    -- which implies $b^{2} \mid a$.
    have h5 : b ^ 2 ∣ a := by
      suffices h : b ^ 2 ∣ -a by exact Int.dvd_neg.mp h
      rw [show -a = 3 * b ^ 2 - a - 3 * b ^ 2 by ring]
      refine Int.dvd_sub h4 ?_
      exact Int.dvd_mul_left 3 (b ^ 2)

    -- We can now write $a=m b^{2}$ with $m$ a positive integer.
    obtain ⟨m, hm⟩ := h5
    have hm_pos : m > 0 := by
      by_contra! h
      have : b ^ 2 * m ≤ 0 := by
        apply mul_nonpos_of_nonneg_of_nonpos
        positivity
        exact h
      linarith

    -- Then $m b^{3}$ is a divisor of $3 b^{2}-m b^{2}$
    have h6 : m * b ^ 3 ∣ 3 * b ^ 2 - m * b ^ 2 := by
      rw [show m * b ^ 3 = a * b by rw [hm]; ring]
      rwa [show m * b ^ 2 = a by rw[hm]; ring]

    -- so $m b$ is a divisor of $3-m$
    have h7 : m * b ∣ 3 - m := by
      rw [show m * b ^ 3 = b ^ 2 * (m * b) by ring] at h6
      rw [show 3 * b ^ 2 - m * b ^ 2 = b ^ 2 * (3 - m) by ring] at h6
      apply Int.dvd_of_mul_dvd_mul_left ?_ h6
      positivity

    -- This implies that $m$ is a divisor of 3 (i.e., $m=1$ or $m=3$)
    have hm_dvd_3 : m ∣ 3 := by
      obtain ⟨k, hk⟩ := h7
      have : m * (b * k + 1) = 3 := by linarith
      exact Dvd.intro (b * k + 1) this

    -- and that $b$ is a divisor of $3-m$.
    have h8 : b ∣ 3 - m := by exact dvd_of_mul_left_dvd h7

    have : m = 3 ∨ m = 1 := by
      have : m ≤ 3 := by apply Int.le_of_dvd; norm_num; exact hm_dvd_3
      interval_cases m
      all_goals norm_num at hm_dvd_3;
      all_goals simp

    rcases this with hm_3 | hm_1
    · -- First, assume $m=3$. Then $a=3 b^{2}$.
      have : a = 3 * b ^ 2 := by rw [hm_3] at hm; rw [hm]; ring
      -- Substituting this gives $M\left(3 b^{2}, b\right)=3 b^{2}-\frac{1}{b}+b^{2}+\frac{1}{b}=4 b^{2}$
      rw [this]
      -- which is the square of $2 b$.
      use 2 * b
      field_simp
      ring
    · -- Now assume $m=1$. From $b \mid 3-m$ we get $b=1$ or $b=2$.
      simp [hm_1] at h8
      have : b ≤ 2 := by apply Int.le_of_dvd; norm_num; exact h8
      interval_cases b
      all_goals rw [hm_1] at hm
      all_goals rw [hm]
      · -- In the first case, $a=1$ and in the second case, $a=4$.
        -- Substituting the first possibility gives $M(1,1)=1-1+1+3=4$, which is a square.
        use 2
        norm_num
      · -- Substituting the second possibility gives $M(4,2)=4-\frac{1}{2}+4+\frac{3}{2}=9$,
        -- which is also a square. We conclude that $M(a, b)$ is a square in all cases.
        use 3
        norm_num

/-(b) Vind gehele getallen $a$ en $b$, beide ongelijk aan nul, zodat $M(a, b)$ een positief geheel getal is, maar geen kwadraat. -/
theorem number_theory_604351_2 : ∃ a b : ℤ, a ≠ 0 ∧ b ≠ 0 ∧
  (∃ k : ℤ, a - 1 / b + b * (b + 3 / a) = k) ∧
  ¬ ∃ z : ℤ, z ^ 2 = (a - 1 / b + b * (b + 3 / a)) := by
    -- Take $a=4$ and $b=-2$. Then $M(4,-2)=7$. This is a positive integer, but not a square.
    use 4, -2
    norm_num
    intro t ht
    have : t ≤ 3 := by nlinarith
    have : t ≥ -3 := by nlinarith
    interval_cases t
    all_goals norm_num at ht
