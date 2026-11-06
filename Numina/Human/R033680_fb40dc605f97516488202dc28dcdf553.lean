import Mathlib

/- Given $$\frac {a+2i}{i}=b+i$$ (where $a$, $b$ are real numbers) and $i$ is the imaginary unit, find $a+b=$ \_\_\_\_\_. -/
theorem algebra_9061 {a b : ℝ} (h : (a + 2 * Complex.I) / Complex.I = b + Complex.I) : a + b = 1 := by
    -- for the equation (a+2i)/i = b+i, multiply both sides i
    have heq: (a+2*Complex.I) / Complex.I * Complex.I = (b+Complex.I)*Complex.I := by rw [h]
    have h2: (a+2*Complex.I)/ Complex.I * Complex.I = a+2*Complex.I := by simp [mul_assoc]
    have h3: (b+Complex.I)*Complex.I = b * Complex.I + Complex.I * Complex.I := by ring
    rw [h2, h3] at heq; simp at heq
    -- now we have (a+2i) = (b+i)i = bi -1 at heq
    have hb: b = 2 := by
        -- for heq, imaginary part of the left side is 2, and right part is b. so b=2.
        have ht1: (a+2*Complex.I).im = 2 := by simp
        have ht2: (b*Complex.I+ -1).im = b := by simp
        have ht3: (a+2*Complex.I).im = (b*Complex.I+ -1).im := by simp [heq]
        rw [ht1, ht2] at ht3
        simp [ht3]
    have ha: a = -1 := by
        -- for heq, real part of the left side is a, and right side is -1. so a = -1.
        have ht1: (a+2*Complex.I).re = a := by simp
        have ht2: (b*Complex.I+ -1).re = -1 := by simp
        have ht3: (a+2*Complex.I).re = (b*Complex.I+ -1).re := by simp [heq]
        rwa [ht1, ht2] at ht3
    norm_num [hb, ha]